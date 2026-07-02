const fs = require('fs');
const path = require('path');

const filePath = process.argv[2] || path.join(__dirname, 'source.txt');
const raw = fs.readFileSync(filePath, 'utf8');

const fragments = raw
  .split(/\r?\n/)
  .map(s => s.trim())
  .filter(s => s.length > 0);

console.log(`Loaded fragments: ${fragments.length}`);

for (const f of fragments) {
  if (!/^\d{2,}$/.test(f)) {
    throw new Error(`Fragment must contain only digits: "${f}"`);
  }
}

const first2 = s => s.slice(0, 2);
const last2 = s => s.slice(-2);

const edgesAll = fragments.map((f, idx) => ({ idx, frag: f, a: first2(f), b: last2(f) }));

const nodeSet = new Set();
for (const e of edgesAll) { nodeSet.add(e.a); nodeSet.add(e.b); }

const adjUndirected = new Map();
for (const n of nodeSet) adjUndirected.set(n, new Set());
for (const e of edgesAll) {
  adjUndirected.get(e.a).add(e.b);
  adjUndirected.get(e.b).add(e.a);
}

function weaklyConnectedComponents() {
  const visited = new Set();
  const comps = [];
  for (const start of nodeSet) {
    if (visited.has(start)) continue;
    const stack = [start];
    visited.add(start);
    const comp = new Set([start]);
    while (stack.length) {
      const v = stack.pop();
      for (const u of adjUndirected.get(v)) {
        if (!visited.has(u)) { visited.add(u); comp.add(u); stack.push(u); }
      }
    }
    comps.push(comp);
  }
  return comps;
}

const components = weaklyConnectedComponents();

class MinCostFlow {
  constructor(n) {
    this.n = n;
    this.graph = Array.from({ length: n }, () => []);
  }
  addEdge(u, v, cap, cost, meta = null) {
    this.graph[u].push({ to: v, cap, cost, flow: 0, meta, rev: this.graph[v].length });
    this.graph[v].push({ to: u, cap: 0, cost: -cost, flow: 0, meta: null, rev: this.graph[u].length - 1 });
  }
  run(s, t, maxFlow) {
    let flow = 0;
    while (flow < maxFlow) {
      const dist = new Array(this.n).fill(Infinity);
      const inQueue = new Array(this.n).fill(false);
      const prevNode = new Array(this.n).fill(-1);
      const prevEdge = new Array(this.n).fill(-1);
      dist[s] = 0;
      const queue = [s];
      inQueue[s] = true;
      while (queue.length) {
        const u = queue.shift();
        inQueue[u] = false;
        for (let i = 0; i < this.graph[u].length; i++) {
          const e = this.graph[u][i];
          if (e.cap - e.flow > 0 && dist[u] + e.cost < dist[e.to]) {
            dist[e.to] = dist[u] + e.cost;
            prevNode[e.to] = u;
            prevEdge[e.to] = i;
            if (!inQueue[e.to]) { inQueue[e.to] = true; queue.push(e.to); }
          }
        }
      }
      if (dist[t] === Infinity) break;
      let aug = maxFlow - flow;
      let v = t;
      while (v !== s) {
        const u = prevNode[v];
        const e = this.graph[u][prevEdge[v]];
        aug = Math.min(aug, e.cap - e.flow);
        v = u;
      }
      v = t;
      while (v !== s) {
        const u = prevNode[v];
        const e = this.graph[u][prevEdge[v]];
        e.flow += aug;
        this.graph[v][e.rev].flow -= aug;
        v = u;
      }
      flow += aug;
    }
    return flow;
  }
}

function shuffle(arr) {
  const a = arr.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function minimalRemovalForBalance(compNodes, compEdges) {
  const nodesArr = shuffle([...compNodes]);
  const edges = shuffle(compEdges);
  const nodeIdx = new Map(nodesArr.map((n, i) => [n, i]));
  const V = nodesArr.length;
  const S = V, T = V + 1;

  const outDeg = new Array(V).fill(0);
  const inDeg = new Array(V).fill(0);
  for (const e of edges) {
    outDeg[nodeIdx.get(e.a)]++;
    inDeg[nodeIdx.get(e.b)]++;
  }
  const excess = outDeg.map((o, i) => o - inDeg[i]);
  const P = excess.filter(x => x > 0).reduce((s, x) => s + x, 0);

  const removed = new Set();
  if (P === 0) return removed;

  const mcmf = new MinCostFlow(V + 2);
  const edgeRef = [];
  for (const e of edges) {
    const u = nodeIdx.get(e.a);
    const before = mcmf.graph[u].length;
    mcmf.addEdge(u, nodeIdx.get(e.b), 1, 1, e.idx);
    edgeRef.push({ u, ei: before });
  }
  for (let i = 0; i < V; i++) {
    if (excess[i] > 0) mcmf.addEdge(S, i, excess[i], 0);
    if (excess[i] < 0) mcmf.addEdge(i, T, -excess[i], 0);
  }

  mcmf.run(S, T, P - 1);

  for (const { u, ei } of edgeRef) {
    const e = mcmf.graph[u][ei];
    if (e.flow > 0) removed.add(e.meta);
  }
  return removed;
}

function hierholzer(nodesArr, edgesList, startNode) {
  const localAdj = new Map();
  for (const n of nodesArr) localAdj.set(n, []);
  for (const e of edgesList) localAdj.get(e.a).push({ to: e.b, frag: e.frag });

  const stackNodes = [startNode];
  const stackFrags = [];
  const circuitFrags = [];

  while (stackNodes.length) {
    const v = stackNodes[stackNodes.length - 1];
    const edges = localAdj.get(v);
    if (edges && edges.length) {
      const e = edges.pop();
      stackNodes.push(e.to);
      stackFrags.push(e.frag);
    } else {
      stackNodes.pop();
      if (stackFrags.length) circuitFrags.push(stackFrags.pop());
    }
  }
  circuitFrags.reverse();
  return circuitFrags;
}

function longestBalancedTrailInKept(keptEdges) {
  const keptNodeSet = new Set();
  for (const e of keptEdges) { keptNodeSet.add(e.a); keptNodeSet.add(e.b); }
  const adj2 = new Map();
  for (const n of keptNodeSet) adj2.set(n, []);
  for (const e of keptEdges) { adj2.get(e.a).push(e.b); adj2.get(e.b).push(e.a); }

  const visited = new Set();
  const subComponents = [];
  for (const start of keptNodeSet) {
    if (visited.has(start)) continue;
    const stack = [start];
    visited.add(start);
    const sc = new Set([start]);
    while (stack.length) {
      const v = stack.pop();
      for (const u of adj2.get(v)) if (!visited.has(u)) { visited.add(u); sc.add(u); stack.push(u); }
    }
    subComponents.push(sc);
  }

  let best = [];
  for (const sc of subComponents) {
    const scEdges = keptEdges.filter(e => sc.has(e.a));
    const outDeg = new Map(), inDeg = new Map();
    for (const n of sc) { outDeg.set(n, 0); inDeg.set(n, 0); }
    for (const e of scEdges) { outDeg.set(e.a, outDeg.get(e.a) + 1); inDeg.set(e.b, inDeg.get(e.b) + 1); }

    let start = null, plus1 = 0, minus1 = 0, bad = 0;
    for (const n of sc) {
      const d = outDeg.get(n) - inDeg.get(n);
      if (d === 1) { start = n; plus1++; }
      else if (d === -1) minus1++;
      else if (d !== 0) bad++;
    }
    if (start === null) {
      for (const n of sc) if (outDeg.get(n) > 0) { start = n; break; }
    }
    if (bad > 0 || plus1 > 1 || minus1 > 1) continue;

    const chain = hierholzer([...sc], scEdges, start);
    if (chain.length > best.length) best = chain;
  }
  return best;
}

function runTrial() {
  let trialBest = [];
  for (const comp of components) {
    const compEdges = edgesAll.filter(e => comp.has(e.a));
    if (compEdges.length === 0) continue;
    const removed = minimalRemovalForBalance(comp, compEdges);
    const keptEdges = compEdges.filter(e => !removed.has(e.idx));
    const chain = longestBalancedTrailInKept(keptEdges);
    if (chain.length > trialBest.length) trialBest = chain;
  }
  return trialBest;
}

const TRIALS = 300;
let overallBest = [];
for (let t = 0; t < TRIALS; t++) {
  const chain = runTrial();
  if (chain.length > overallBest.length) overallBest = chain;
}

let result = overallBest.length ? overallBest[0] : '';
for (let i = 1; i < overallBest.length; i++) result += overallBest[i].slice(2);

console.log(`Fragments used: ${overallBest.length} of ${fragments.length}`);
console.log(`Final number length: ${result.length}`);
console.log('Fragment chain:');
console.log(overallBest.join(' & '));
console.log('Answer:');
console.log(result);
