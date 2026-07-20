#!/usr/bin/env python3
"""Pages 4-6 diagrams: the router forest witness; counting methods; separation methods."""
import drawsvg as dw

INK = '#22223b'; GREY = '#8a8fa3'; LGREY = '#e7e9f0'
TEAL = '#0f766e'; TEALBG = '#e9f5f3'
BLUE = '#1d4ed8'; BLUEBG = '#eaf0fd'
AMBER = '#b45309'; AMBERBG = '#fdf3e7'
RED = '#b91c1c'; REDBG = '#fdecec'
GREEN = '#15803d'; GREENBG = '#eaf6ee'
VIOLET = '#6d28d9'; VIOLETBG = '#f1ebfc'
F = 'Helvetica'

def mk_helpers(d):
    markers = {}
    def arrow_marker(color, mid):
        m = dw.Marker(-0.1, -5, 10, 5, scale=1, orient='auto', id=mid)
        m.append(dw.Lines(-0.1, -4, 9, 0, -0.1, 4, close=True, fill=color))
        d.append(m)
        return m
    for i, c in enumerate([INK, TEAL, BLUE, AMBER, RED, GREY, GREEN, VIOLET]):
        markers[c] = arrow_marker(c, f'ah{i}')
    def line(x1, y1, x2, y2, color=INK, w=2.0, dash=None, arrow=True):
        kw = dict(stroke=color, stroke_width=w, fill='none')
        if dash: kw['stroke_dasharray'] = dash
        if arrow: kw['marker_end'] = markers[color]
        d.append(dw.Line(x1, y1, x2, y2, **kw))
    def box(x, y, w, h, fill, stroke, rx=9, sw=1.6, dash=None):
        kw = dict(rx=rx, fill=fill, stroke=stroke, stroke_width=sw)
        if dash: kw['stroke_dasharray'] = dash
        d.append(dw.Rectangle(x, y, w, h, **kw))
    def txt(s, x, y, size=15, color=INK, anchor='middle', weight='normal', style=None):
        kw = dict(font_size=size, font_family=F, fill=color, text_anchor=anchor, font_weight=weight)
        if style: kw['font_style'] = style
        d.append(dw.Text(s, x=x, y=y, **kw))
    def zone(x, y, w, label, color):
        d.append(dw.Rectangle(x, y, w, 28, rx=14, fill=color, opacity=0.14))
        txt(label, x + w/2, y + 19.5, 16, color, weight='bold')
    return line, box, txt, zone

# ==================================================================
# PAGE 4: THE FOREST  (1660 x 860)
# ==================================================================
d = dw.Drawing(1660, 860, origin=(0, 0))
d.append(dw.Rectangle(0, 0, 1660, 860, fill='white'))
line, box, txt, zone = mk_helpers(d)

# ---------- (a) a program is a tree ----------
zone(18, 14, 780, 'A PROGRAM IS A TREE  ·  drawn from the construction', TEAL)

def node_box(x, y, gate, leaf, color=TEAL, bg=TEALBG):
    box(x-78, y-24, 156, 48, bg, color, rx=8)
    txt(gate, x, y-5, 12.5, INK)
    txt('post-map  ' + leaf, x, y+14, 11.5, color, weight='bold')

def base_box(x, y, lbl):
    box(x-46, y-17, 92, 34, 'white', GREY, rx=8, sw=1.3)
    txt(lbl, x, y+4, 12, INK)

# level-2 code over the counting world: gates are thresholds, k = 2
node_box(400, 90, 'gate: is x ≥ 3 ?', 'flip')
node_box(205, 205, 'gate: is x ≥ 5 ?', 'id')
node_box(595, 205, 'gate: is x ≥ 1 ?', 'flip')
base_box(120, 320, 'cell u₀'); base_box(290, 320, 'cell u₁')
base_box(510, 320, 'cell u₂'); base_box(680, 320, 'cell u₁')
line(360, 116, 240, 180, INK, 1.8); txt('no', 285, 142, 11, GREY)
line(440, 116, 560, 180, INK, 1.8); txt('yes', 515, 142, 11, GREY)
line(175, 231, 130, 300, INK, 1.6); txt('no', 140, 262, 10.5, GREY)
line(235, 231, 282, 300, INK, 1.6); txt('yes', 272, 262, 10.5, GREY)
line(565, 231, 520, 300, INK, 1.6); txt('no', 530, 262, 10.5, GREY)
line(625, 231, 672, 300, INK, 1.6); txt('yes', 662, 262, 10.5, GREY)
txt('one candidate = one finite tree: a gate picks a child by a threshold on the input,', 400, 372, 12.5, INK)
txt('the chosen child answers, the node’s post-map finishes.  The compute family is', 400, 390, 12.5, INK)
txt('constitutive: an elementary cell at every base, a finite post-map at every node.', 400, 408, 12.5, INK)
txt('free selection is forbidden by the machine’s own theorem: with unrestricted', 400, 430, 11.5, GREY)
txt('selectors, one step reaches every function, so candidates must be trees (data).', 400, 446, 11.5, GREY)

# ---------- (b) the tower ----------
zone(830, 14, 810, 'THE TOWER  ·  strict at every rung, priced at every rung', BLUE)
txt('capacity ≤ 2^(depth+1), proved at every rung', 1235, 66, 12.5, INK)
BOT = 352
widths = [200, 340, 480, 620]
heights = [82, 150, 218, 272]
shades = ['#dae4fb', '#e4ecfd', '#eef3fe', '#f7f9ff']
for lvl in [3, 2, 1, 0]:
    w, h = widths[lvl], heights[lvl]
    box(1235 - w/2, BOT - h, w, h, shades[3 - lvl], BLUE, rx=12, sw=1.4)
    txt(f'depth {lvl}', 1235 - w/2 + 42, BOT - h + 20, 12, BLUE, weight='bold')
for lvl in range(3):
    sx = 1235 + (widths[lvl] + widths[lvl + 1]) / 4
    sy = BOT - heights[lvl] - 14
    txt('★', sx, sy + 4, 15, RED)
    txt('escapes', sx + 46, sy + 3, 10.5, RED)
txt('every rung strictly larger, on the counting world and on the real-vector world;', 1235, BOT + 46, 12.5, INK)
txt('the union over all depths never exhausts the function space.  Retrieval over', 1235, BOT + 64, 12.5, INK)
txt('depth-sorted candidates returns a least-depth fit: built-in simplicity bias.', 1235, BOT + 82, 12.5, INK)
txt('the machine of page one runs verbatim over this forest: same retrieval, same laws.', 1235, BOT + 106, 11.5, GREY)

# ---------- (c) modify by grafting ----------
zone(18, 470, 780, 'MODIFY BY GRAFTING  ·  the first rung climbs, in one picture', AMBER)

def tiny_node(x, y, gate, leaf, color=AMBER, bg=AMBERBG, w=120):
    box(x-w/2, y-20, w, 40, bg, color, rx=7, sw=1.4)
    txt(gate, x, y-3, 10.5, INK)
    txt(leaf, x, y+12, 10.5, color, weight='bold')

# context with hole
txt('modifier: one hole', 130, 528, 12.5, AMBER, weight='bold')
tiny_node(130, 570, 'gate: always right', 'post-map flip')
base_box(62, 660, 'cell u₁')
d.append(dw.Circle(198, 660, 26, fill='white', stroke=AMBER, stroke_width=1.8, stroke_dasharray='5,4'))
txt('hole', 198, 664, 11, AMBER, weight='bold')
line(100, 592, 70, 638, INK, 1.5); line(160, 592, 192, 634, INK, 1.5)
txt('+', 300, 630, 30, INK)
# anchor
txt('accepted anchor', 385, 528, 12.5, TEAL, weight='bold')
base_box(385, 630, 'cell u₀')
txt('⇒', 480, 630, 30, INK)
# grafted result
txt('grafted program', 640, 528, 12.5, GREEN, weight='bold')
tiny_node(640, 570, 'gate: always right', 'post-map flip', GREEN, GREENBG)
base_box(572, 660, 'cell u₁')
box(700-46, 660-17, 92, 34, TEALBG, TEAL, rx=8, sw=1.6)
txt('cell u₀', 700, 664, 12, INK)
line(610, 592, 580, 638, INK, 1.5); line(670, 592, 696, 634, INK, 1.5)
txt('grafting is part of the grammar: a plugged modifier IS a tree, so modified programs', 400, 726, 12.3, INK)
txt('inherit every law.  Here the gate always routes to the graft and the post-map flips it:', 400, 744, 12.3, INK)
txt('the grafted program disagrees with its anchor on every input.  One modifier, one rung.', 400, 762, 12.3, INK)
txt('retrieval over modifiers = grafting: the accepted anchor enters every candidate by the hole.', 400, 786, 11.5, GREY)

# ---------- (d) dichotomy ----------
zone(830, 470, 810, 'FREE IS FLAT, BOUND CLIMBS  ·  the dichotomy', VIOLET)
# axes
ax0, ay0, axw, ayh = 900, 760, 480, 210
line(ax0, ay0, ax0 + axw, ay0, INK, 1.8, arrow=True)
line(ax0, ay0, ax0, ay0 - ayh, INK, 1.8, arrow=True)
txt('modifier depth', ax0 + axw/2, ay0 + 26, 12, GREY)
txt('reachable programs', ax0 - 14, ay0 - ayh - 10, 12, GREY, anchor='start')
# flat line
line(ax0, ay0 - 52, ax0 + axw - 20, ay0 - 52, RED, 2.6, dash='7,5', arrow=False)
txt('free modifiers: flat at the object class (any depth collapses to one step)', ax0 + 236, ay0 - 62, 11.5, RED)
# climbing staircase
sx, sy = ax0, ay0 - 20
steps = [(0, 20), (110, 58), (220, 96), (330, 134), (440, 172)]
for i in range(len(steps) - 1):
    (x1, h1), (x2, h2) = steps[i], steps[i+1]
    line(ax0 + x1, ay0 - h1, ax0 + x2, ay0 - h1, GREEN, 2.6, arrow=False)
    line(ax0 + x2, ay0 - h1, ax0 + x2, ay0 - h2, GREEN, 2.6, arrow=False)
txt('grammar-bound modifiers climb the tower', ax0 + 250, ay0 - 190, 12, GREEN, weight='bold')
txt('embedding within two rungs; strict climb proved at stride three;', 1235, 806, 11.8, INK)
txt('in the limit the graft loses nothing: the bound ladder fills the whole tower.', 1235, 824, 11.8, INK)
txt('certificates chain at every storey (page two); the per-storey capacity product prices execution.', 1235, 846, 11.3, GREY)

d.save_svg('/Users/polaris/Documents/Epistemology and Zetesis/Projects/transformer-learning-theory/machine_card/machine_forest.svg')
print('forest SVG OK')

# ==================================================================
# PAGE 5: COUNTING MADE VISIBLE  (1660 x 620)
# ==================================================================
d = dw.Drawing(1660, 620, origin=(0, 0))
d.append(dw.Rectangle(0, 0, 1660, 620, fill='white'))
line, box, txt, zone = mk_helpers(d)

# ---------- (A) flip counter ----------
zone(18, 14, 790, 'REVISION ACCOUNTING BY POTENTIALS', BLUE)
# value trace
vals = ['c₁', 'c₁', 'c₃', 'c₃', 'c₃', 'c₄', 'c₄', 'c₄']
phis = [5, 5, 3, 3, 3, 1, 1, 1]
bx0, by0 = 70, 90
for i, v in enumerate(vals):
    changed = i > 0 and vals[i] != vals[i-1]
    box(bx0 + i*88, by0, 74, 36, REDBG if changed else 'white', RED if changed else GREY, rx=7, sw=1.5)
    txt(v, bx0 + i*88 + 37, by0 + 23, 13.5, INK)
    if changed:
        txt('flip', bx0 + i*88 + 37, by0 - 8, 11, RED, weight='bold')
txt('the answer along one run', bx0 + 2, by0 - 26, 12, GREY, anchor='start')
# potential staircase
py = 220
for i, p in enumerate(phis):
    h = p * 14
    box(bx0 + i*88, py + (70 - h), 74, h, BLUEBG, BLUE, rx=4, sw=1.2)
    txt(str(p), bx0 + i*88 + 37, py + 88, 12, BLUE)
txt('the potential: survivors φ (never rises; drops at every flip)', bx0 + 2, py - 10, 12, GREY, anchor='start')
box(bx0 + 180, py + 116, 420, 40, GREENBG, GREEN, rx=9)
txt('2 flips  +  1 remaining  ≤  5 at the start', bx0 + 390, py + 141, 14.5, GREEN, weight='bold')
txt('to bound revisions of ANY dial, exhibit one non-rising quantity that drops when the dial moves;', 413, 408, 12.3, INK)
txt('the count plus what remains never exceeds what you started with.  All revision laws are this line.', 413, 426, 12.3, INK)

# ---------- (B) counting through the image ----------
zone(850, 14, 790, 'COUNTING AT THE GRANULARITY OF BEHAVIOR', AMBER)
cx0 = 930
for i in range(6):
    box(cx0 + (i % 6)*92, 80, 76, 32, 'white', GREY, rx=7, sw=1.3)
    txt(f'code {i+1}', cx0 + (i % 6)*92 + 38, 101, 12, INK)
models = ['model A', 'model A', 'model B', 'model B', 'model B', 'model C']
targets = {'model A': 990, 'model B': 1230, 'model C': 1470}
for i, mname in enumerate(models):
    line(cx0 + i*92 + 38, 116, targets[mname], 172, GREY, 1.4)
for mx, mname in [(990, 'model A'), (1230, 'model B'), (1470, 'model C')]:
    box(mx - 60, 176, 120, 36, AMBERBG, AMBER, rx=8)
    txt(mname, mx, 199, 13, INK)
txt('six encodings, three behaviors: revisions are priced by the three behaviors;', 1245, 250, 12.3, INK)
txt('the duplicate encodings cost nothing.  A one-to-one map makes the bound exact.', 1245, 268, 12.3, INK)
txt('a count that factors through a map is priced by the image; duplicates cost nothing.', 1245, 292, 11.5, GREY)

# ---------- (C) survivor floor ----------
zone(850, 330, 790, 'THE CONSISTENT SET AS CANONICAL STATE', TEAL)
sy0 = 392
sets = [('after  s₁', [1,1,1,1,0,1,1,0]), ('after  s₁ s₂', [0,1,1,1,0,0,1,0]), ('after  s₁ s₂ s₃', [0,1,0,1,0,0,0,0])]
for r, (lbl, bits) in enumerate(sets):
    txt(lbl, 1005, sy0 + r*54 + 21, 12.5, TEAL, anchor='end')
    for i, b in enumerate(bits):
        box(1020 + i*66, sy0 + r*54, 54, 30, TEALBG if b else LGREY, TEAL if b else GREY, rx=6, sw=1.2)
        txt(f'c{i+1}', 1020 + i*66 + 27, sy0 + r*54 + 20, 11.5, INK if b else GREY)
txt('append evidence = intersect survivor sets: order-free, only shrinking, and an empty set stays empty.', 1245, 590, 12.0, INK)

# ---------- (D) settling by well-ordering ----------
zone(18, 452 - 6, 790, 'ENUMERATION OVER A WELL-ORDER', GREEN)
wy = 512
line(70, wy + 44, 780, wy + 44, INK, 1.8)
for i in range(6):
    x = 110 + i*112
    alive = (i == 2)
    box(x - 34, wy + 10, 68, 34, GREENBG if alive else 'white', GREEN if alive else GREY, rx=8, sw=1.6 if alive else 1.2)
    txt(f'{i}', x, wy + 32, 13, GREEN if alive else GREY, weight='bold' if alive else 'normal')
    if i < 2:
        txt(f'dies at t={2 + 3*i}', x, wy + 62, 11, RED)
    if i == 2:
        txt('fits forever', x, wy + 62, 11, GREEN, weight='bold')
    if i > 2:
        txt('never asked', x, wy + 62, 11, GREY)
txt('…', 790, wy + 34, 16, GREY)
txt('each candidate below the least fitting one dies at a finite time; past the last death the least fit is', 413, 596, 12.0, INK)
txt('selected forever.  No size bound needed: the ordering does the work of finiteness.', 413, 613, 12.0, INK)

d.save_svg('/Users/polaris/Documents/Epistemology and Zetesis/Projects/transformer-learning-theory/machine_card/machine_methods1.svg')
print('methods1 SVG OK')

# ==================================================================
# PAGE 6: SEPARATION MADE VISIBLE  (1660 x 620)
# ==================================================================
d = dw.Drawing(1660, 620, origin=(0, 0))
d.append(dw.Rectangle(0, 0, 1660, 620, fill='white'))
line, box, txt, zone = mk_helpers(d)

# ---------- (A) darkness cured only by enlargement ----------
zone(18, 14, 790, 'INDISTINGUISHABILITY UNDER A QUERY CLASS', RED)
hy = 78
tests = ['read 1', 'read 2', 'read 3', 'read 4']
for j, t in enumerate(tests):
    txt(t, 250 + j*110, hy - 8, 11.5, GREY)
txt('enlarged read', 720, hy - 8, 11.5, VIOLET, weight='bold')
for r, mech in enumerate(['object M', 'object M′']):
    yy = hy + 12 + r*56
    box(60, yy, 130, 38, 'white', INK, rx=8)
    txt(mech, 125, yy + 24, 12.5, INK)
    for j in range(4):
        box(205 + j*110, yy, 90, 38, LGREY, GREY, rx=7, sw=1.1)
        txt('same', 250 + j*110, yy + 24, 12, GREY)
    box(660, yy, 120, 38, VIOLETBG, VIOLET, rx=7, sw=1.6)
    txt('0' if r == 0 else '1', 720, yy + 25, 14, VIOLET, weight='bold')
txt('two DIFFERENT objects, identical under every read in the family: indistinguishable.', 413, 218, 12.3, INK)
txt('enlarging the family is what separates them; repeating the existing reads does nothing.', 413, 236, 12.3, INK)
txt('on the causal store of page three, the family is observation and the enlarging read is an intervention.', 413, 260, 11.5, GREY)

# ---------- (B) the limit escapes every finite view ----------
zone(850, 14, 790, 'TWO-SIDED LOCATION OF LIMIT EVENTS', BLUE)
ey = 92
for i in range(6):
    box(920 + i*112, ey, 96, 40, BLUEBG, BLUE, rx=8, sw=1.2)
    txt(f'first {i+1} words', 968 + i*112, ey + 25, 10.5, INK)
txt('…', 1608, ey + 27, 16, GREY)
box(1000, ey + 84, 500, 42, 'white', RED, rx=9, sw=1.8, dash='6,4')
txt('the limit event: which model the run settles on', 1250, ey + 110, 12.5, RED)
for i in range(6):
    line(968 + i*112, ey + 44, 1180 + (i-2)*28, ey + 82, GREY, 1.1, arrow=False)
txt('no single finite view decides it; a countable union of countable intersections', 1245, 268, 12.3, INK)
txt('of finite views captures it exactly.  Hardness and definability, located together.', 1245, 286, 12.3, INK)

# ---------- (C) flat where it computes, stacked where it certifies ----------
zone(18, 330, 1622, 'THE COLLAPSE TEST FOR LAYERED SYSTEMS', GREEN)
cy = 420
# computation lane
txt('computation', 96, cy - 26, 12.5, GREY)
for i, lbl in enumerate(['anchor c₀', 'storey 1', 'storey 2', 'storey 3']):
    box(60 + i*250, cy - 18, 170, 40, TEALBG if i == 0 else 'white', TEAL, rx=9)
    txt(lbl, 145 + i*250, cy + 7, 12.5, INK)
    if i < 3:
        line(230 + i*250, cy + 2, 310 + i*250, cy + 2, TEAL, 2.0)
txt('=', 1105, cy + 8, 26, INK)
box(1150, cy - 18, 210, 40, TEALBG, TEAL, rx=9)
txt('ONE storey, composed', 1255, cy + 7, 12.5, INK)
txt('(collapse is definitional)', 1255, cy + 44, 11, GREY)
# certificate lane
cy2 = 540
txt('certificates', 96, cy2 - 26, 12.5, GREY)
for i, lbl in enumerate(['fit + least, stage 1', 'fit + least, stage 2', 'fit + least, stage 3']):
    box(60 + i*330, cy2 - 18, 250, 40, GREENBG, GREEN, rx=9)
    txt(lbl, 185 + i*330, cy2 + 7, 12.5, INK)
    if i < 2:
        line(310 + i*330, cy2 + 2, 390 + i*330, cy2 + 2, GREEN, 2.0)
        txt('conditional on', 350 + i*330, cy2 - 12, 10.5, GREEN)
box(1080, cy2 - 18, 540, 40, 'white', GREEN, rx=9, sw=1.8)
txt('the chain NEVER collapses: every storey keeps its own freeze', 1350, cy2 + 7, 12.5, GREEN, weight='bold')
txt('ask of any layered system: what collapses, and what stacks.  Here: the decode collapses (depth is free for', 830, 600, 12.3, INK)
txt('computing), the certificate chain stacks (depth is real exactly for trust).  The price compounds per storey.', 830, 618, 12.3, INK)

d.save_svg('/Users/polaris/Documents/Epistemology and Zetesis/Projects/transformer-learning-theory/machine_card/machine_methods2.svg')
print('methods2 SVG OK')
