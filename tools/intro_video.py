#!/usr/bin/env python3
"""The landing intro video for RS^N³ · Hidrógeno: frames written as PNG for ffmpeg.

Story, 12 s at 30 fps:
  0.0-1.5  Black space: nothing has happened yet
  1.0-3.5  The integer lattice [-M,M]^3 appears, hopping links drawn along the 6 axes
  2.5-7.0  The nucleus at (0,0,0) ignites; Bloch sphere (d=2) spins; Coulomb hops travel
  5.5-8.5  Corner nodes glow purple: defect rho(4) = 0.0729 opens for d >= 4
  7.5-9.8  Lattice settles into canonical isometric view
  9.0-12.0 Title and subtitle fade in:
           RS^N³ · Hidrógeno
           el átomo en enteros · Lean 4 · Mathlib

Usage: tools/intro_video.py OUTDIR   (then tools/intro_video.sh encodes it)
"""
import math
import random
import sys
from pathlib import Path

from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageFont

W, H, SS = 1920, 1080, 2          # Output size and supersampling
FPS, SECONDS = 30, 12.0
BG = (6, 8, 11)                   # #06080b
BLUE = (91, 155, 230)             # #5b9be6
INK = (242, 241, 238)             # #f2f1ee
MUTED = (138, 137, 133)           # #8a8985
WARM = (240, 138, 93)             # #f08a5d
PURPLE = (178, 102, 255)          # #b266ff
CX, CY, A = 960, 420, 130         # Centre and scale
ISO_AZ, ISO_EL = -math.pi / 4, math.atan(1 / math.sqrt(2))
FONT_BOLD = "/usr/share/fonts/open-sans/OpenSans-Semibold.ttf"
FONT_REG = "/usr/share/fonts/open-sans/OpenSans-Regular.ttf"

# Integer cube [-1, 1]^3 = 27 nodes
NODES = [(i, j, k) for i in (-1, 0, 1) for j in (-1, 0, 1) for k in (-1, 0, 1)]
NUCLEUS_IDX = 13  # (0, 0, 0)
CORNERS = [idx for idx, (i, j, k) in enumerate(NODES) if abs(i) == 1 and abs(j) == 1 and abs(k) == 1]
EDGES = [(a, b) for a in range(27) for b in range(a + 1, 27)
         if sum(abs(NODES[a][t] - NODES[b][t]) for t in range(3)) == 1]


def clamp(x, lo=0.0, hi=1.0):
    return max(lo, min(hi, x))


def ease(x):
    x = clamp(x)
    return x * x * (3 - 2 * x)


def ramp(t, t0, t1):
    return ease((t - t0) / (t1 - t0))


def project(p, az, el):
    """Orthographic view: turn by `az` about vertical axis, tilt by `el`."""
    x, y, z = p
    x1, y1 = x * math.cos(az) - y * math.sin(az), x * math.sin(az) + y * math.cos(az)
    depth = y1 * math.cos(el) - z * math.sin(el)
    up = y1 * math.sin(el) + z * math.cos(el)
    s = A / math.cos(ISO_EL)
    return CX + s * x1, CY - s * up, depth


def mix(c, k):
    return tuple(int(BG[t] + (c[t] - BG[t]) * k) for t in range(3))


def frame(t, pulses, font_t, font_s):
    big = (W * SS, H * SS)
    base = Image.new("RGB", big, BG)
    glow = Image.new("RGB", big, (0, 0, 0))
    d, g = ImageDraw.Draw(base), ImageDraw.Draw(glow)
    S = lambda v: int(v * SS)

    settle = ramp(t, 7.5, 9.8)
    az = ISO_AZ - (1 - settle) * (0.6 + 1.25 * math.pi * (1 - ramp(t, 1.0, 9.8)))
    el = ISO_EL - (1 - settle) * 0.28
    pts = [project(p, az, el) for p in NODES]

    appear = [ramp(t, 1.0 + 0.05 * n, 1.6 + 0.05 * n) for n in range(27)]
    links = ramp(t, 1.8, 3.8)
    nuc_ignite = ramp(t, 2.2, 3.8)
    corner_glow = ramp(t, 5.5, 7.5) * (1 - ramp(t, 8.8, 10.0))
    light = ramp(t, 3.0, 4.2) * (1 - ramp(t, 8.6, 9.6))

    # Hopping excitation pulses
    heat = [0.0] * 27
    for (a, b, t0) in pulses:
        u = (t - t0) / 0.65
        if 0 <= u <= 1 and light > 0:
            (xa, ya, _), (xb, yb, _) = pts[a], pts[b]
            x, y = xa + (xb - xa) * u, ya + (yb - ya) * u
            col = mix(WARM if a == NUCLEUS_IDX or b == NUCLEUS_IDX else BLUE, light)
            for rr, cc in ((24, col), (8, mix(INK, light))):
                g.ellipse([S(x - rr), S(y - rr), S(x + rr), S(y + rr)], fill=cc)
        if 0.85 <= u <= 1.5:
            heat[b] = max(heat[b], light * (1 - abs(u - 1.0) / 0.5))

    # Links: 6-axis hopping lines
    for a, b in EDGES:
        k = links * min(appear[a], appear[b])
        if k <= 0:
            continue
        (xa, ya, _), (xb, yb, _) = pts[a], pts[b]
        xe, ye = xa + (xb - xa) * k, ya + (yb - ya) * k
        is_nuc_axis = (a == NUCLEUS_IDX or b == NUCLEUS_IDX)
        col = mix(WARM if is_nuc_axis and nuc_ignite > 0.3 else BLUE, 0.45 + 0.25 * (heat[a] + heat[b]))
        d.line([S(xa), S(ya), S(xe), S(ye)], fill=col, width=S(2.2 if is_nuc_axis else 1.8))

    # Nucleus Bloch sphere halo at (0,0,0)
    nx, ny, _ = pts[NUCLEUS_IDX]
    if nuc_ignite > 0:
        pulse = 0.5 + 0.5 * math.sin(t * 4.0)
        nr = S(48 + 12 * pulse * nuc_ignite)
        g.ellipse([S(nx) - nr, S(ny) - nr, S(nx) + nr, S(ny) + nr], fill=mix(WARM, 0.45 * nuc_ignite))
        # Bloch equator ring
        bx, by = S(nx), S(ny)
        d.arc([bx - S(32), by - S(14), bx + S(32), by + S(14)], 0, 360, fill=mix(WARM, 0.85 * nuc_ignite), width=S(2))
        # Spin vector precession
        spin_ang = t * 2.5
        sx = bx + S(28 * math.cos(spin_ang))
        sy = by - S(28 * math.sin(spin_ang) * 0.7)
        d.line([bx, by, sx, sy], fill=mix(INK, nuc_ignite), width=S(2.5))
        d.ellipse([sx - S(4), sy - S(4), sx + S(4), sy + S(4)], fill=mix(WARM, nuc_ignite))

    # Corner defect cones (d >= 4)
    if corner_glow > 0:
        for c in CORNERS:
            cx, cy, _ = pts[c]
            cr = S(26)
            g.ellipse([S(cx) - cr, S(cy) - cr, S(cx) + cr, S(cy) + cr], fill=mix(PURPLE, 0.55 * corner_glow))

    # Lattice sites
    for n in sorted(range(27), key=lambda n: -pts[n][2]):
        if appear[n] <= 0:
            continue
        x, y, _ = pts[n]
        if n == NUCLEUS_IDX:
            r = S(9 + 2 * nuc_ignite)
            d.ellipse([S(x) - r, S(y) - r, S(x) + r, S(y) + r], fill=mix(WARM, appear[n]))
            g.ellipse([S(x) - S(20), S(y) - S(20), S(x) + S(20), S(y) + S(20)], fill=mix(WARM, 0.8 * nuc_ignite))
        elif n in CORNERS and corner_glow > 0:
            r = S(6)
            d.ellipse([S(x) - r, S(y) - r, S(x) + r, S(y) + r], fill=mix(PURPLE, corner_glow))
        else:
            r = S(5.5 * appear[n])
            d.ellipse([S(x) - r, S(y) - r, S(x) + r, S(y) + r], fill=mix(INK, appear[n]))
            if heat[n] > 0:
                rr = S(18)
                g.ellipse([S(x) - rr, S(y) - rr, S(x) + rr, S(y) + rr], fill=mix(BLUE, 0.7 * heat[n]))

    out = ImageChops.add(base, glow.filter(ImageFilter.GaussianBlur(S(8))))

    # Title & Subtitle typography
    ti, su = ramp(t, 9.0, 10.2), ramp(t, 9.7, 10.9)
    od = ImageDraw.Draw(out)
    if ti > 0:
        dy = (1 - ti) * 16
        od.text((S(960), S(830 + dy)), "RS^N³ · Hidrógeno", font=font_t, fill=mix(INK, ti), anchor="ms")
    if su > 0:
        od.text((S(960), S(900)), "el átomo en enteros · Lean 4 · Mathlib", font=font_s,
                fill=mix(MUTED, su), anchor="ms")
    return out.resize((W, H), Image.LANCZOS)


def main():
    if len(sys.argv) < 2:
        print("Usage: intro_video.py OUTDIR")
        sys.exit(1)
    out = Path(sys.argv[1])
    out.mkdir(parents=True, exist_ok=True)
    rnd = random.Random(1934)
    adj = {n: [] for n in range(27)}
    for a, b in EDGES:
        adj[a].append(b)
        adj[b].append(a)
    pulses, walkers = [], [NUCLEUS_IDX, 0, 26, 4, 22]
    t0 = 3.0
    while t0 < 8.6:
        for w in range(len(walkers)):
            nxt = rnd.choice(adj[walkers[w]])
            pulses.append((walkers[w], nxt, t0 + 0.1 * w))
            walkers[w] = nxt
        t0 += 0.55
    font_t = ImageFont.truetype(FONT_BOLD, 92 * SS)
    font_s = ImageFont.truetype(FONT_REG, 34 * SS)
    total_frames = int(FPS * SECONDS)
    for f in range(total_frames):
        frame(f / FPS, pulses, font_t, font_s).save(out / f"f{f:04d}.png")


if __name__ == "__main__":
    main()
