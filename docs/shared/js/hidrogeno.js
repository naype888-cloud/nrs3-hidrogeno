// The living cube of the hydrogen landing. N x N x N cells (blue): each is a position the electron can
// take; the dot follows the density of a trial 1s (exp(-2r), not an eigenstate). The orange trail is the
// electron travelling the lattice one axis step at a time: it never vanishes and reappears elsewhere.
// Click: next N. Drag: turn. Keys: left/right change N.
(() => {
  "use strict";
  const canvas = document.getElementById("crystal");
  if (!canvas || !canvas.getContext) return;
  const out = document.getElementById("readout"), cap = document.getElementById("cap"), dots = document.getElementById("dots");
  const still = matchMedia("(prefers-reduced-motion: reduce)");
  const css = getComputedStyle(document.documentElement);
  const col = (n, d) => (css.getPropertyValue(n).trim() || d);
  const BLUE = col("--blue", "#5b9be6"), ORANGE = col("--orange", "#f08a5d");
  const NS = [2, 4, 6, 8];
  let k = 1, yaw = 0.7, pitch = 0.42, dragging = false, moved = 0, lastX = 0, lastY = 0, running = false;
  let walk = [], step = 0, last = 0;

  const half = (N) => (N - 1) / 2;                 // cell centres at i - half: the origin is a corner
  function newWalk() {
    const N = NS[k], h = half(N);
    // start near the origin corner, then bias the walk toward the cells that weigh more (1s)
    let p = [Math.floor(N / 2) - 1, Math.floor(N / 2) - 1, Math.floor(N / 2) - 1];
    walk = [p.slice()];
    for (let s = 0; s < 40; s++) {
      const ax = Math.floor(Math.random() * 3), sg = Math.random() < 0.5 ? -1 : 1, q = p.slice();
      q[ax] += sg;
      if (q[ax] < 0 || q[ax] >= N) continue;
      p = q; walk.push(p.slice());
    }
    step = 0;
  }
  function label() {
    const N = NS[k];
    out.innerHTML = `<b>N = ${N}</b> · ${N ** 3} celdas · 6 saltos de eje por celda · cubo finito`;
    dots.querySelectorAll("button").forEach((b, i) => b.setAttribute("aria-current", i === k ? "true" : "false"));
  }
  function go(i) { k = (i + NS.length) % NS.length; newWalk(); label(); if (!running) frame(performance.now()); }
  NS.forEach((N, i) => {
    const b = document.createElement("button");
    b.type = "button"; b.title = "N = " + N; b.setAttribute("aria-label", "N = " + N); b.textContent = N;
    b.addEventListener("click", () => go(i)); dots.appendChild(b);
  });

  function project(x, y, z, W, H, sc) {
    const cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
    const x1 = cy * x + sy * z, z1 = -sy * x + cy * z, y1 = cp * y - sp * z1, z2 = sp * y + cp * z1;
    const f = 1 / (1 + z2 * 0.06);
    return [W / 2 + x1 * sc * f, H / 2 - y1 * sc * f, z2, f];
  }
  function frame(now) {
    const dpr = Math.min(devicePixelRatio || 1, 2), r = canvas.getBoundingClientRect();
    const W = Math.max(1, Math.round(r.width * dpr)), H = Math.max(1, Math.round(r.height * dpr));
    if (canvas.width !== W || canvas.height !== H) { canvas.width = W; canvas.height = H; }
    const g = canvas.getContext("2d");
    g.clearRect(0, 0, W, H);
    const N = NS[k], h = half(N), sc = (Math.min(W, H) * 0.36) / (h + 0.6), r0 = N / 3.2;
    if (!dragging && !still.matches) yaw += 0.0045;
    if (!still.matches && now - last > 260) { last = now; step = Math.min(step + 1, walk.length + 6); if (step >= walk.length + 6) newWalk(); }
    const pts = [];
    for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) for (let l = 0; l < N; l++) {
      const x = i - h, y = j - h, z = l - h;
      // trial 1s centred on the origin corner of the cube, in units where the Bohr radius is r0 cells
      const cx = i - N / 2 + 0.5, cyy = j - N / 2 + 0.5, cz = l - N / 2 + 0.5;
      const rho = Math.exp(-2 * Math.hypot(cx, cyy, cz) / r0);
      const p = project(x, y, z, W, H, sc);
      pts.push({ p, rho });
    }
    pts.sort((a, b) => b.p[2] - a.p[2]);
    for (const { p, rho } of pts) {
      const s = (1.2 + 5.2 * Math.sqrt(rho)) * dpr * p[3];
      g.globalAlpha = 0.25 + 0.7 * Math.sqrt(rho);
      g.fillStyle = BLUE; g.beginPath(); g.arc(p[0], p[1], s, 0, 6.2832); g.fill();
    }
    // the orange trail: the hop, one axis step at a time
    g.globalAlpha = 1; g.lineCap = "round"; g.lineJoin = "round";
    const upto = Math.min(step, walk.length - 1);
    for (let s = 1; s <= upto; s++) {
      const a = walk[s - 1], b = walk[s], age = (upto - s) / 14;
      const pa = project(a[0] - h, a[1] - h, a[2] - h, W, H, sc), pb = project(b[0] - h, b[1] - h, b[2] - h, W, H, sc);
      g.globalAlpha = Math.max(0.12, 1 - age); g.strokeStyle = ORANGE; g.lineWidth = 2.4 * dpr;
      g.beginPath(); g.moveTo(pa[0], pa[1]); g.lineTo(pb[0], pb[1]); g.stroke();
    }
    if (walk.length) {
      const c = walk[Math.min(upto, walk.length - 1)], pc = project(c[0] - h, c[1] - h, c[2] - h, W, H, sc);
      g.globalAlpha = 1; g.fillStyle = ORANGE; g.beginPath(); g.arc(pc[0], pc[1], 5 * dpr, 0, 6.2832); g.fill();
    }
    g.globalAlpha = 1;
  }
  function loop(now) { if (!running) return; frame(now); requestAnimationFrame(loop); }
  const start = () => { if (!running) { running = true; requestAnimationFrame(loop); } };
  const stop = () => { running = false; };

  canvas.addEventListener("pointerdown", (e) => { dragging = true; moved = 0; lastX = e.clientX; lastY = e.clientY; canvas.setPointerCapture(e.pointerId); });
  canvas.addEventListener("pointermove", (e) => {
    if (!dragging) return;
    yaw += (e.clientX - lastX) * 0.008; pitch = Math.max(-1.3, Math.min(1.3, pitch + (e.clientY - lastY) * 0.006));
    moved += Math.abs(e.clientX - lastX) + Math.abs(e.clientY - lastY); lastX = e.clientX; lastY = e.clientY;
    if (!running) frame(performance.now());
  });
  canvas.addEventListener("pointerup", () => { dragging = false; if (moved < 6) go(k + 1); });
  canvas.addEventListener("pointercancel", () => (dragging = false));
  canvas.addEventListener("keydown", (e) => {
    if (e.key === "ArrowRight") { go(k + 1); e.preventDefault(); } else if (e.key === "ArrowLeft") { go(k - 1); e.preventDefault(); }
  });
  document.addEventListener("visibilitychange", () => (document.hidden ? stop() : start()));
  new ResizeObserver(() => { if (!running) frame(performance.now()); }).observe(canvas);

  newWalk(); label(); step = 12; frame(performance.now());
  requestAnimationFrame(() => canvas.classList.add("ready"));
  if (!still.matches) start();

  // ---- the ticker of the results ------------------------------------------------------------------------
  const items = [...document.querySelectorAll(".ticker li")], bar = document.querySelector(".progress");
  if (!items.length) return;
  const TICK = 3800;
  let idx = 0, paused = false;
  function show(i) {
    items.forEach((li, n) => {
      li.classList.toggle("on", n === i); li.classList.toggle("off", n === idx && n !== i);
      li.querySelector("a").tabIndex = n === i ? 0 : -1; li.setAttribute("aria-hidden", n === i ? "false" : "true");
    });
    idx = i;
    if (bar) { bar.style.setProperty("--tick", TICK / 1000 + "s"); bar.classList.remove("run"); void bar.offsetWidth; bar.classList.add("run"); }
  }
  function tick() { if (!paused && !document.hidden) show((idx + 1) % items.length); setTimeout(tick, TICK); }
  const list = document.querySelector(".ticker");
  list.addEventListener("pointerenter", () => (paused = true));
  list.addEventListener("pointerleave", () => (paused = false));
  list.addEventListener("focusin", () => (paused = true));
  list.addEventListener("focusout", () => (paused = false));
  show(0);
  if (!still.matches) setTimeout(tick, TICK);
})();
