import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const moves = 'udlr'; // Opposite directions have indices d ^ 1.
const optimalLimit = 24000;
const fallbackLimit = 32000;

function parse(text) {
  const rows = text.trimEnd().split(/\r?\n/);
  const width = Math.max(...rows.map(row => row.length));
  const cells = rows.map(row => row.padEnd(width, '#')).join('');
  const offsets = [-width, width, -1, 1];
  return { cells, offsets, width, player: cells.search(/[@+]/) };
}

// Start at each doorway and flood only its side of the hall. Include the
// hallway square at the threshold so the player can stand behind a door box.
function rooms(board) {
  const { cells, width, player, offsets } = board;
  const hall = Math.floor(player / width) * width;
  const result = [];
  for (let x = 1; x < width - 1; x++) {
    const entrance = hall + x;
    for (const vertical of offsets.slice(0, 2)) {
      const door = entrance + vertical;
      if (cells[door] === '#') continue;
      const squares = [entrance, door];
      const index = new Map([[entrance, 0], [door, 1]]);
      for (let head = 1; head < squares.length; head++) {
        for (const delta of offsets) {
          const q = squares[head] + delta;
          if (cells[q] === '#' || index.has(q) || (q >= hall && q < hall + width)) continue;
          index.set(q, squares.length);
          squares.push(q);
        }
      }
      const neighbors = squares.map(p => offsets.map(delta => index.get(p + delta) ?? -1));
      const boxes = [], goals = [];
      squares.forEach((p, i) => {
        if ('$*'.includes(cells[p])) boxes.push(i);
        if ('.*+'.includes(cells[p])) goals.push(i);
      });
      result.push({ squares, neighbors, boxes, goals });
    }
  }
  return result;
}

// A reverse push needs both a source for the box and a stance for the
// player. Ignoring other boxes gives an admissible distance to each goal.
function goalDistances(neighbors, goal) {
  const distance = Array(neighbors.length).fill(Infinity);
  const queue = [goal];
  distance[goal] = 0;
  for (let head = 0; head < queue.length; head++) {
    const p = queue[head];
    for (let d = 0; d < 4; d++) {
      const q = neighbors[p][d];
      if (q < 0 || neighbors[q][d] < 0 || distance[q] !== Infinity) continue;
      distance[q] = distance[p] + 1;
      queue.push(q);
    }
  }
  return distance;
}

function solveRoom({ squares, neighbors, boxes: initial, goals }) {
  const n = squares.length;
  const distances = goals.map(goal => goalDistances(neighbors, goal));
  const estimates = new Map();
  const boxKey = boxes => boxes.reduce((key, p) => key * n + p, 0);
  function estimate(boxes, key) {
    if (estimates.has(key)) return estimates.get(key);
    let best = Infinity;
    function assign(i, used, total) {
      if (total >= best) return;
      if (i === boxes.length) { best = total; return; }
      for (let g = 0; g < goals.length; g++) {
        if (!(used & (1 << g))) assign(i + 1, used | (1 << g), total + distances[g][boxes[i]]);
      }
    }
    assign(0, 0, 0);
    estimates.set(key, best);
    return best;
  }

  const occupied = new Uint8Array(n);
  const seen = new Uint32Array(n);
  const queue = new Uint8Array(n);
  let stamp = 0;
  // The smallest reachable square names the player's entire walkable region.
  function region(player) {
    ++stamp;
    let least = player, end = 1;
    queue[0] = player;
    seen[player] = stamp;
    for (let head = 0; head < end; head++) {
      for (const q of neighbors[queue[head]]) {
        if (q < 0 || occupied[q] || seen[q] === stamp) continue;
        seen[q] = stamp;
        queue[end++] = q;
        if (q < least) least = q;
      }
    }
    return least;
  }

  // Integer priority buckets. Equal-priority pushes are explored last-in-first-out.
  function search(weight, limit) {
    const buckets = [];
    const bestDepth = new Map();
    let first = Infinity;
    function add(boxes, player, depth, parent, from, direction) {
      const arrangement = boxKey(boxes);
      const h = estimate(boxes, arrangement);
      if (!Number.isFinite(h)) return; // Includes dead squares and impossible matchings.
      const key = arrangement * n + region(player);
      if ((bestDepth.get(key) ?? Infinity) <= depth) return;
      bestDepth.set(key, depth);
      const priority = depth + weight * h;
      (buckets[priority] ??= []).push({ boxes, player, depth, parent, from, direction, key, h });
      first = Math.min(first, priority);
    }
    occupied.fill(0);
    for (const b of initial) occupied[b] = 1;
    add(initial, 0, 0, null, -1, -1);
    let expanded = 0;
    while (first < buckets.length && expanded < limit) {
      if (!buckets[first]?.length) { first++; continue; }
      const node = buckets[first].pop();
      if (bestDepth.get(node.key) !== node.depth) continue;
      if (node.h === 0) {
        const pushes = [];
        for (let p = node; p.parent; p = p.parent) pushes.push([squares[p.from], p.direction]);
        return pushes.reverse();
      }
      expanded++;
      occupied.fill(0);
      for (const b of node.boxes) occupied[b] = 1;
      region(node.player);
      const reachableStamp = stamp;
      const candidates = [];
      for (const [i, b] of node.boxes.entries()) {
        for (let d = 0; d < 4; d++) {
          const to = neighbors[b][d], behind = neighbors[b][d ^ 1];
          if (to >= 0 && !occupied[to] && seen[behind] === reachableStamp)
            candidates.push([i, b, d, to]);
        }
      }
      for (const [i, b, d, to] of candidates) {
        const boxes = node.boxes.slice();
        boxes[i] = to;
        boxes.sort((a, b) => a - b);
        occupied[b] = 0;
        occupied[to] = 1;
        add(boxes, b, node.depth + 1, node, b, d);
        occupied[b] = 1;
        occupied[to] = 0;
      }
    }
    return null;
  }
  return search(1, optimalLimit) ?? search(4, fallbackLimit);
}

// Only after search, expand the chosen pushes into actual player moves.
function solve(text) {
  const board = parse(text);
  const { cells, offsets } = board;
  const blocked = Uint8Array.from(cells, ch => '#$*'.includes(ch) ? 1 : 0);
  let player = board.player;
  const answer = [];
  for (const room of rooms(board)) {
    const pushes = solveRoom(room);
    if (!pushes) return '';
    for (const [box, d] of pushes) {
      const stance = box - offsets[d];
      const via = new Int8Array(cells.length).fill(-1);
      const queue = [player];
      via[player] = 4;
      for (let head = 0; head < queue.length && via[stance] < 0; head++) {
        for (let step = 0; step < 4; step++) {
          const q = queue[head] + offsets[step];
          if (blocked[q] || via[q] !== -1) continue;
          via[q] = step;
          queue.push(q);
        }
      }
      if (via[stance] < 0) throw new Error('Unreachable push stance');
      const walk = [];
      for (let q = stance; q !== player; q -= offsets[via[q]]) walk.push(moves[via[q]]);
      answer.push(walk.reverse().join(''), moves[d].toUpperCase());
      blocked[box] = 0;
      blocked[box + offsets[d]] = 1;
      player = box;
    }
  }
  return answer.join('');
}

const input = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const output = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(input).sort()) {
  const solution = solve(readFileSync(join(input, id, 'level.txt'), 'utf8'));
  mkdirSync(join(output, id), { recursive: true });
  writeFileSync(join(output, id, 'solution.txt'), solution + '\n');
}
