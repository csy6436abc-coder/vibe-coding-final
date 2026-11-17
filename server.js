'use strict';
const express = require('express');
const http = require('http');
const path = require('path');
const { Server } = require('socket.io');

const PORT = Number(process.env.PORT) || 3000;
const BOT_COUNT = process.env.BOT_COUNT !== undefined ? Number(process.env.BOT_COUNT) : 10;

// Agar.io-style rules: radius = sqrt(mass * 100), food = 1 mass, start = 10 mass
const W = 7000;
const H = 7000;
const TICK_MS = 40;
const FOOD_TARGET = 2000;
const FOOD_SPAWN_PER_TICK = 25;
const FOOD_R = 10;
const START_MASS = 10;
const MIN_SPLIT_MASS = 35;
const MIN_EJECT_MASS = 35;
const EJECT_COST = 18;
const EJECT_MASS = 13;
const EJECT_COOLDOWN_MS = 80;
const MAX_CELLS = 16;
const MAX_CELL_MASS = 22500;
const EAT_RATIO = 1.25;
const VIRUS_MASS = 100;
const VIRUS_COUNT = 25;
const VIRUS_MAX = 50;
const VIRUS_FEED_COUNT = 7;
const VIRUS_POP_RATIO = 1.33;
const DECAY_PER_SEC = 0.002;
const BOOST_DECAY = 7;
const GRID = 200;
const COLS = Math.ceil(W / GRID);
const ROWS = Math.ceil(H / GRID);
const MAX_PELLETS = 1500;

const FOOD_COLORS = [
  '#ff5a5a', '#ffa64d', '#ffe14d', '#8cff4d', '#4dff88', '#4dffe1',
  '#4db8ff', '#4d6bff', '#a64dff', '#ff4dd2', '#ff8fab', '#c9ff4d'
];
const PLAYER_COLORS = [
  '#ff3b3b', '#ff8a00', '#ffd400', '#7ed321', '#00c853', '#00bfa5',
  '#00b0ff', '#2962ff', '#7c4dff', '#d500f9', '#ff4081', '#8d6e63'
];
const BOT_NAMES = [
  '먹보', '세포왕', 'Blob', 'Nom', '하마', '도토리', 'Mitosis', 'Amoeba',
  '젤리', 'Bubble', '쿠키', 'Pac', '구름', 'Mochi', '두부', 'Pixel'
];

const massToR = m => Math.sqrt(m * 100);
const speedFor = r => 2200 * Math.pow(r, -0.439);
const mergeDelay = m => (30 + 0.0233 * m) * 1000;
const clamp = (v, lo, hi) => (v < lo ? lo : v > hi ? hi : v);
const rnd = (lo, hi) => lo + Math.random() * (hi - lo);
const pick = arr => arr[Math.floor(Math.random() * arr.length)];
const viewZoom = (sumR, w, h) => Math.pow(Math.min(64 / sumR, 1), 0.4) * Math.max(h / 1080, w / 1920);

const players = new Map();
const food = new Map();
const foodGrid = Array.from({ length: COLS * ROWS }, () => new Set());
const pellets = new Map();
const viruses = new Map();
let nextId = 1;
let nextPid = 1;
let foodAdded = [];
let foodRemoved = [];

function gridIndex(x, y) {
  return clamp(Math.floor(x / GRID), 0, COLS - 1) + clamp(Math.floor(y / GRID), 0, ROWS - 1) * COLS;
}

function addFood() {
  const f = {
    id: nextId++,
    x: Math.round(rnd(FOOD_R, W - FOOD_R)),
    y: Math.round(rnd(FOOD_R, H - FOOD_R)),
    c: Math.floor(Math.random() * FOOD_COLORS.length)
  };
  f.g = gridIndex(f.x, f.y);
  food.set(f.id, f);
  foodGrid[f.g].add(f);
  foodAdded.push(f.id, f.x, f.y, f.c);
}

function removeFood(f) {
  food.delete(f.id);
  foodGrid[f.g].delete(f);
  foodRemoved.push(f.id);
}

function addVirus(x, y, bvx = 0, bvy = 0) {
  const v = { id: nextId++, x, y, m: VIRUS_MASS, r: massToR(VIRUS_MASS), feed: 0, bvx, bvy };
  viruses.set(v.id, v);
}

function setMass(c, m) {
  c.m = m;
  c.r = massToR(m);
}

function totalMass(p) {
  let m = 0;
  for (const c of p.cells) m += c.m;
  return m;
}

function dirTo(c, tx, ty) {
  const dx = tx - c.x, dy = ty - c.y;
  const d = Math.hypot(dx, dy);
  return d < 1 ? [1, 0] : [dx / d, dy / d];
}

function clampCell(c) {
  c.x = clamp(c.x, Math.min(c.r, W / 2), Math.max(W - c.r, W / 2));
  c.y = clamp(c.y, Math.min(c.r, H / 2), Math.max(H - c.r, H / 2));
}

function createPlayer({ name, socket = null, isBot = false }) {
  const p = {
    pid: nextPid++, name, color: pick(PLAYER_COLORS), socket, isBot,
    cells: [], alive: false, mx: 0, my: 0, lastEject: 0,
    view: { w: 1920, h: 1080 }, stats: null, killer: null, respawnAt: 0, wander: null
  };
  players.set(p.pid, p);
  return p;
}

function newCell(p, x, y, m) {
  return { id: nextId++, p, x, y, m, r: massToR(m), bvx: 0, bvy: 0, mergeAt: 0, dead: false };
}

function findSpawn() {
  let best = null, bestGap = -Infinity;
  for (let t = 0; t < 15; t++) {
    const x = rnd(300, W - 300), y = rnd(300, H - 300);
    let gap = Infinity;
    for (const q of players.values()) {
      for (const c of q.cells) {
        if (c.m < 40) continue;
        gap = Math.min(gap, Math.hypot(c.x - x, c.y - y) - c.r);
      }
    }
    if (gap > 600) return { x, y };
    if (gap > bestGap) { bestGap = gap; best = { x, y }; }
  }
  return best;
}

function spawn(p) {
  const pos = findSpawn();
  p.cells = [newCell(p, pos.x, pos.y, START_MASS)];
  p.alive = true;
  p.mx = pos.x;
  p.my = pos.y;
  p.killer = null;
  p.stats = { food: 0, cells: 0, best: START_MASS, start: Date.now(), topRank: Infinity };
}

function splitCell(p, cell, nx, ny, now) {
  const half = cell.m / 2;
  setMass(cell, half);
  const child = newCell(p, cell.x, cell.y, half);
  const dist = child.r * 2.5 + 260;
  child.bvx = nx * dist * BOOST_DECAY;
  child.bvy = ny * dist * BOOST_DECAY;
  cell.mergeAt = child.mergeAt = now + mergeDelay(half);
  p.cells.push(child);
}

function splitPlayer(p) {
  if (!p.alive) return;
  const now = Date.now();
  const list = p.cells.filter(c => c.m >= MIN_SPLIT_MASS).sort((a, b) => b.m - a.m);
  for (const c of list) {
    if (p.cells.length >= MAX_CELLS) break;
    const [nx, ny] = dirTo(c, p.mx, p.my);
    splitCell(p, c, nx, ny, now);
  }
}

function ejectPlayer(p) {
  const now = Date.now();
  if (!p.alive || now - p.lastEject < EJECT_COOLDOWN_MS) return;
  p.lastEject = now;
  const r = massToR(EJECT_MASS);
  for (const c of p.cells) {
    if (c.m < MIN_EJECT_MASS) continue;
    const [dx, dy] = dirTo(c, p.mx, p.my);
    const a = Math.atan2(dy, dx) + (Math.random() - 0.5) * 0.2;
    const nx = Math.cos(a), ny = Math.sin(a);
    setMass(c, c.m - EJECT_COST);
    const id = nextId++;
    pellets.set(id, {
      id, pid: p.pid, m: EJECT_MASS, r,
      x: clamp(c.x + nx * c.r, r, W - r),
      y: clamp(c.y + ny * c.r, r, H - r),
      bvx: nx * 520 * BOOST_DECAY, bvy: ny * 520 * BOOST_DECAY,
      nx, ny, safeUntil: now + 500
    });
  }
  while (pellets.size > MAX_PELLETS) pellets.delete(pellets.keys().next().value);
}

function popCell(p, c, v, now) {
  setMass(c, c.m + v.m);
  const free = MAX_CELLS - p.cells.length;
  const n = Math.min(free, Math.floor((c.m * 0.5) / 12));
  if (n <= 0) return;
  const pm = (c.m * 0.5) / n;
  setMass(c, c.m - pm * n);
  c.mergeAt = now + mergeDelay(c.m);
  const off = Math.random() * Math.PI * 2;
  for (let i = 0; i < n; i++) {
    const a = off + (i / n) * Math.PI * 2;
    const nc = newCell(p, c.x, c.y, pm);
    const dist = nc.r * 2.5 + 200;
    nc.bvx = Math.cos(a) * dist * BOOST_DECAY;
    nc.bvy = Math.sin(a) * dist * BOOST_DECAY;
    nc.mergeAt = now + mergeDelay(pm);
    p.cells.push(nc);
  }
}

function feedVirus(v, pel) {
  setMass(v, v.m + pel.m);
  v.feed++;
  if (v.feed < VIRUS_FEED_COUNT) return;
  v.feed = 0;
  setMass(v, VIRUS_MASS);
  if (viruses.size >= VIRUS_MAX) return;
  addVirus(v.x, v.y, pel.nx * 750 * BOOST_DECAY, pel.ny * 750 * BOOST_DECAY);
}

function nearestFood(x, y, ring) {
  const gx = clamp(Math.floor(x / GRID), 0, COLS - 1);
  const gy = clamp(Math.floor(y / GRID), 0, ROWS - 1);
  let best = null, bestD = Infinity;
  for (let j = Math.max(0, gy - ring); j <= Math.min(ROWS - 1, gy + ring); j++) {
    for (let i = Math.max(0, gx - ring); i <= Math.min(COLS - 1, gx + ring); i++) {
      for (const f of foodGrid[i + j * COLS]) {
        const d = (f.x - x) ** 2 + (f.y - y) ** 2;
        if (d < bestD) { bestD = d; best = f; }
      }
    }
  }
  return best;
}

function botThink(b) {
  let me = b.cells[0];
  for (const c of b.cells) if (c.m > me.m) me = c;
  const range = 500 + me.r * 3;
  let threat = null, threatGap = Infinity, prey = null, preyScore = 0;

  for (const q of players.values()) {
    if (q === b || !q.alive) continue;
    for (const c of q.cells) {
      const dx = c.x - me.x, dy = c.y - me.y;
      if (Math.abs(dx) > range || Math.abs(dy) > range) continue;
      const d = Math.hypot(dx, dy);
      if (c.m > me.m * EAT_RATIO) {
        const gap = d - c.r - me.r;
        if (gap < threatGap) { threatGap = gap; threat = c; }
      } else if (me.m > c.m * EAT_RATIO) {
        const s = c.m / (d + 50);
        if (s > preyScore) { preyScore = s; prey = c; }
      }
    }
  }
  if (me.m > VIRUS_MASS * VIRUS_POP_RATIO) {
    for (const v of viruses.values()) {
      const gap = Math.hypot(v.x - me.x, v.y - me.y) - v.r - me.r;
      if (gap < 60 && gap < threatGap) { threatGap = gap; threat = v; }
    }
  }

  if (threat && threatGap < 300) {
    const dx = me.x - threat.x, dy = me.y - threat.y;
    const d = Math.hypot(dx, dy) || 1;
    b.mx = clamp(me.x + (dx / d) * 800, 0, W);
    b.my = clamp(me.y + (dy / d) * 800, 0, H);
    return;
  }
  if (prey) {
    b.mx = prey.x;
    b.my = prey.y;
    const d = Math.hypot(prey.x - me.x, prey.y - me.y);
    if (b.cells.length < 4 && me.m >= MIN_SPLIT_MASS && me.m / 2 > prey.m * EAT_RATIO &&
        d < me.r * 2.5 + 200 && Math.random() < 0.1) {
      splitPlayer(b);
    }
    return;
  }
  const f = nearestFood(me.x, me.y, 2);
  if (f) { b.mx = f.x; b.my = f.y; return; }
  if (!b.wander || Math.hypot(b.wander.x - me.x, b.wander.y - me.y) < 100) {
    b.wander = { x: rnd(200, W - 200), y: rnd(200, H - 200) };
  }
  b.mx = b.wander.x;
  b.my = b.wander.y;
}

function moveCells(dt) {
  const k = Math.exp(-BOOST_DECAY * dt);
  for (const p of players.values()) {
    if (!p.alive) continue;
    for (const c of p.cells) {
      const dx = p.mx - c.x, dy = p.my - c.y;
      const d = Math.hypot(dx, dy);
      if (d > 1) {
        const step = Math.min(speedFor(c.r) * Math.min(1, d / 64) * dt, d);
        c.x += (dx / d) * step;
        c.y += (dy / d) * step;
      }
      if (c.bvx || c.bvy) {
        c.x += c.bvx * dt;
        c.y += c.bvy * dt;
        c.bvx *= k;
        c.bvy *= k;
        if (Math.abs(c.bvx) + Math.abs(c.bvy) < 5) c.bvx = c.bvy = 0;
      }
      clampCell(c);
    }
  }
}

function resolveOwnCells(now) {
  for (const p of players.values()) {
    const cs = p.cells;
    if (!p.alive || cs.length < 2) continue;
    for (let i = 0; i < cs.length; i++) {
      const a = cs[i];
      if (a.dead) continue;
      for (let j = i + 1; j < cs.length; j++) {
        const b = cs[j];
        if (b.dead) continue;
        let dx = b.x - a.x, dy = b.y - a.y;
        let d = Math.hypot(dx, dy);
        const rs = a.r + b.r;
        if (d >= rs) continue;

        if (now >= a.mergeAt && now >= b.mergeAt) {
          const big = a.m >= b.m ? a : b;
          const small = big === a ? b : a;
          if (d < big.r) {
            setMass(big, big.m + small.m);
            small.dead = true;
            if (a.dead) break;
          }
          continue;
        }
        // Freshly split cells fly through their siblings until the boost wears off
        if (Math.abs(a.bvx) + Math.abs(a.bvy) > 150 || Math.abs(b.bvx) + Math.abs(b.bvy) > 150) continue;
        if (d < 0.001) { dx = Math.random() - 0.5; dy = Math.random() - 0.5; d = Math.hypot(dx, dy); }
        const overlap = rs - d;
        const nx = dx / d, ny = dy / d;
        const tot = a.m + b.m;
        a.x -= nx * overlap * (b.m / tot);
        a.y -= ny * overlap * (b.m / tot);
        b.x += nx * overlap * (a.m / tot);
        b.y += ny * overlap * (a.m / tot);
      }
    }
  }
}

function moveProjectiles(dt) {
  const k = Math.exp(-BOOST_DECAY * dt);
  for (const group of [pellets, viruses]) {
    for (const o of group.values()) {
      if (!o.bvx && !o.bvy) continue;
      o.x = clamp(o.x + o.bvx * dt, o.r, W - o.r);
      o.y = clamp(o.y + o.bvy * dt, o.r, H - o.r);
      o.bvx *= k;
      o.bvy *= k;
      if (Math.abs(o.bvx) + Math.abs(o.bvy) < 5) o.bvx = o.bvy = 0;
    }
  }
}

function eatFood() {
  for (const p of players.values()) {
    if (!p.alive) continue;
    for (const c of p.cells) {
      const x0 = clamp(Math.floor((c.x - c.r) / GRID), 0, COLS - 1);
      const x1 = clamp(Math.floor((c.x + c.r) / GRID), 0, COLS - 1);
      const y0 = clamp(Math.floor((c.y - c.r) / GRID), 0, ROWS - 1);
      const y1 = clamp(Math.floor((c.y + c.r) / GRID), 0, ROWS - 1);
      const r2 = c.r * c.r;
      let gained = 0;
      for (let gy = y0; gy <= y1; gy++) {
        for (let gx = x0; gx <= x1; gx++) {
          for (const f of foodGrid[gx + gy * COLS]) {
            const dx = f.x - c.x, dy = f.y - c.y;
            if (dx * dx + dy * dy < r2) { removeFood(f); gained++; }
          }
        }
      }
      if (gained) {
        setMass(c, c.m + gained);
        p.stats.food += gained;
      }
    }
  }
}

function eatPellets(now) {
  for (const pel of pellets.values()) {
    let eaten = false;
    for (const p of players.values()) {
      if (!p.alive || (p.pid === pel.pid && now < pel.safeUntil)) continue;
      for (const c of p.cells) {
        if (c.dead || c.r < pel.r) continue;
        const dx = pel.x - c.x, dy = pel.y - c.y;
        if (Math.abs(dx) > c.r || Math.abs(dy) > c.r) continue;
        if (dx * dx + dy * dy < c.r * c.r) {
          setMass(c, c.m + pel.m);
          eaten = true;
          break;
        }
      }
      if (eaten) break;
    }
    if (eaten) { pellets.delete(pel.id); continue; }
    for (const v of viruses.values()) {
      if ((pel.x - v.x) ** 2 + (pel.y - v.y) ** 2 < v.r * v.r) {
        feedVirus(v, pel);
        pellets.delete(pel.id);
        break;
      }
    }
  }
}

function popViruses(now) {
  for (const v of viruses.values()) {
    let popped = false;
    for (const p of players.values()) {
      if (!p.alive) continue;
      for (const c of p.cells) {
        if (c.dead || c.m < v.m * VIRUS_POP_RATIO) continue;
        if (Math.hypot(v.x - c.x, v.y - c.y) < c.r - v.r / 3) {
          popCell(p, c, v, now);
          popped = true;
          break;
        }
      }
      if (popped) break;
    }
    if (popped) viruses.delete(v.id);
  }
}

function eatCells() {
  const all = [];
  for (const p of players.values()) {
    if (!p.alive) continue;
    for (const c of p.cells) if (!c.dead) all.push(c);
  }
  all.sort((a, b) => b.m - a.m);
  for (let i = 0; i < all.length; i++) {
    const a = all[i];
    if (a.dead) continue;
    for (let j = i + 1; j < all.length; j++) {
      const b = all[j];
      if (b.dead || b.p === a.p || a.m < b.m * EAT_RATIO) continue;
      const dx = b.x - a.x, dy = b.y - a.y;
      if (Math.abs(dx) > a.r || Math.abs(dy) > a.r) continue;
      if (Math.hypot(dx, dy) < a.r - b.r / 3) {
        setMass(a, a.m + b.m);
        b.dead = true;
        a.p.stats.cells++;
        b.p.killer = a.p.name;
      }
    }
  }
}

function decayAndCap(dt, now) {
  for (const p of players.values()) {
    if (!p.alive) continue;
    const n = p.cells.length;
    for (let i = 0; i < n; i++) {
      const c = p.cells[i];
      if (c.dead) continue;
      if (c.m > MIN_SPLIT_MASS) setMass(c, c.m - c.m * DECAY_PER_SEC * dt);
      if (c.m > MAX_CELL_MASS) {
        if (p.cells.length < MAX_CELLS) {
          const [nx, ny] = dirTo(c, p.mx, p.my);
          splitCell(p, c, nx, ny, now);
        } else {
          setMass(c, MAX_CELL_MASS);
        }
      }
    }
  }
}

function kill(p, now) {
  p.alive = false;
  p.cells = [];
  if (p.isBot) {
    p.respawnAt = now + rnd(2000, 5000);
    return;
  }
  p.socket.emit('dead', {
    killer: p.killer,
    best: Math.floor(p.stats.best),
    time: Math.floor((now - p.stats.start) / 1000),
    food: p.stats.food,
    cells: p.stats.cells,
    rank: p.stats.topRank === Infinity ? null : p.stats.topRank
  });
}

function cleanup(now) {
  for (const p of players.values()) {
    if (!p.alive) continue;
    if (p.cells.some(c => c.dead)) p.cells = p.cells.filter(c => !c.dead);
    if (p.cells.length === 0) { kill(p, now); continue; }
    for (const c of p.cells) clampCell(c);
    const m = totalMass(p);
    if (m > p.stats.best) p.stats.best = m;
  }
  while (viruses.size < VIRUS_COUNT) addVirus(rnd(300, W - 300), rnd(300, H - 300));
  for (let i = 0; i < FOOD_SPAWN_PER_TICK && food.size < FOOD_TARGET; i++) addFood();
}

function broadcast() {
  const fa = foodAdded, fd = foodRemoved;
  for (const p of players.values()) {
    if (p.isBot || !p.alive) continue;
    let cx = 0, cy = 0, sumR = 0;
    for (const c of p.cells) { cx += c.x; cy += c.y; sumR += c.r; }
    cx /= p.cells.length;
    cy /= p.cells.length;
    const z = viewZoom(sumR, p.view.w, p.view.h);
    const hw = p.view.w / 2 / z + 300;
    const hh = p.view.h / 2 / z + 300;

    const cs = [];
    for (const q of players.values()) {
      if (!q.alive) continue;
      for (const c of q.cells) {
        if (Math.abs(c.x - cx) < hw + c.r && Math.abs(c.y - cy) < hh + c.r) {
          cs.push(c.id, q.pid, Math.round(c.x), Math.round(c.y), Math.round(c.r));
        }
      }
    }
    const es = [];
    for (const e of pellets.values()) {
      if (Math.abs(e.x - cx) < hw && Math.abs(e.y - cy) < hh) es.push(e.id, Math.round(e.x), Math.round(e.y), e.pid);
    }
    const vs = [];
    for (const v of viruses.values()) {
      if (Math.abs(v.x - cx) < hw + v.r && Math.abs(v.y - cy) < hh + v.r) {
        vs.push(v.id, Math.round(v.x), Math.round(v.y), Math.round(v.r));
      }
    }
    p.socket.emit('s', { c: cs, e: es, v: vs, fa, fd });
  }
}

let lastTick = Date.now();
let tickNo = 0;
function tick() {
  const now = Date.now();
  const dt = Math.min((now - lastTick) / 1000, 0.1);
  lastTick = now;
  tickNo++;

  for (const p of players.values()) {
    if (!p.isBot) continue;
    if (!p.alive) { if (now >= p.respawnAt) spawn(p); continue; }
    if ((tickNo + p.pid) % 3 === 0) botThink(p);
  }

  moveCells(dt);
  resolveOwnCells(now);
  moveProjectiles(dt);
  eatFood();
  eatPellets(now);
  popViruses(now);
  eatCells();
  decayAndCap(dt, now);
  cleanup(now);
  broadcast();
  foodAdded = [];
  foodRemoved = [];
}

function leaderboard() {
  const ranked = [];
  for (const p of players.values()) if (p.alive) ranked.push({ p, m: totalMass(p) });
  ranked.sort((a, b) => b.m - a.m);
  const top = ranked.slice(0, 10).map(x => x.p.pid);
  ranked.forEach(({ p }, i) => {
    if (i + 1 < p.stats.topRank) p.stats.topRank = i + 1;
    if (!p.isBot) p.socket.emit('lb', { t: top, r: i + 1 });
  });
}

function sanitizeName(name) {
  return String(name ?? '').replace(/[\u0000-\u001f\u007f]/g, '').trim().slice(0, 15);
}

function setView(p, d) {
  if (!d || typeof d !== 'object') return;
  p.view.w = clamp(Number(d.w) || 1920, 320, 3840);
  p.view.h = clamp(Number(d.h) || 1080, 240, 2160);
}

// World setup
for (let i = 0; i < FOOD_TARGET; i++) addFood();
foodAdded = [];
for (let i = 0; i < VIRUS_COUNT; i++) addVirus(rnd(300, W - 300), rnd(300, H - 300));
for (let i = 0; i < BOT_COUNT; i++) spawn(createPlayer({ name: BOT_NAMES[i % BOT_NAMES.length], isBot: true }));

const app = express();
const server = http.createServer(app);
const io = new Server(server, { transports: ['websocket', 'polling'] });

app.use(express.static(path.join(__dirname, 'public')));

io.on('connection', socket => {
  let player = null;

  socket.emit('hello', {
    W, H, foodR: FOOD_R, ejectR: massToR(EJECT_MASS), foodColors: FOOD_COLORS,
    pinfo: [...players.values()].map(p => [p.pid, p.name, p.color])
  });

  socket.on('join', data => {
    if (!data || typeof data !== 'object') return;
    const name = sanitizeName(data.name);
    if (!player) player = createPlayer({ name, socket });
    else player.name = name;
    setView(player, data);
    if (player.alive) return;
    spawn(player);
    io.emit('pi', [player.pid, player.name, player.color]);
    const fs = [];
    for (const f of food.values()) fs.push(f.id, f.x, f.y, f.c);
    socket.emit('init', { pid: player.pid, food: fs });
  });

  socket.on('m', d => {
    if (!player || !Array.isArray(d)) return;
    const x = Number(d[0]), y = Number(d[1]);
    if (!Number.isFinite(x) || !Number.isFinite(y)) return;
    player.mx = clamp(x, 0, W);
    player.my = clamp(y, 0, H);
  });
  socket.on('split', () => { if (player) splitPlayer(player); });
  socket.on('eject', () => { if (player) ejectPlayer(player); });
  socket.on('view', d => { if (player) setView(player, d); });
  socket.on('p', cb => { if (typeof cb === 'function') cb(); });

  socket.on('disconnect', () => {
    if (!player) return;
    players.delete(player.pid);
    io.emit('pl', player.pid);
  });
});

setInterval(tick, TICK_MS);
setInterval(leaderboard, 500);

server.listen(PORT, () => console.log(`Cell Wars running on port ${PORT} (bots: ${BOT_COUNT})`));
