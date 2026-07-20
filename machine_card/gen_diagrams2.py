#!/usr/bin/env python3
"""Page-2 cascade diagram + page-3 witness-by-construction diagram."""
import drawsvg as dw

INK = '#22223b'; GREY = '#8a8fa3'; LGREY = '#e7e9f0'
TEAL = '#0f766e'; TEALBG = '#e9f5f3'
BLUE = '#1d4ed8'; BLUEBG = '#eaf0fd'
AMBER = '#b45309'; AMBERBG = '#fdf3e7'
RED = '#b91c1c'; REDBG = '#fdecec'; GREEN = '#15803d'; GREENBG = '#eaf6ee'
F = 'Helvetica'

def mk(d):
    marks = {}
    for i, c in enumerate([INK, TEAL, BLUE, AMBER, RED, GREY, GREEN]):
        m = dw.Marker(-0.1, -5, 10, 5, scale=1, orient='auto', id=f'a{i}')
        m.append(dw.Lines(-0.1, -4, 9, 0, -0.1, 4, close=True, fill=c))
        d.append(m); marks[c] = m
    return marks

def helpers(d, MK):
    def line(x1, y1, x2, y2, color=INK, w=2.0, dash=None, arrow=True):
        kw = dict(stroke=color, stroke_width=w, fill='none')
        if dash: kw['stroke_dasharray'] = dash
        if arrow: kw['marker_end'] = MK[color]
        d.append(dw.Line(x1, y1, x2, y2, **kw))
    def box(x, y, w, h, fill, stroke, rx=9, sw=1.6):
        d.append(dw.Rectangle(x, y, w, h, rx=rx, fill=fill, stroke=stroke, stroke_width=sw))
    def txt(s, x, y, size=13, color=INK, anchor='middle', weight='normal'):
        d.append(dw.Text(s, x=x, y=y, font_size=size, font_family=F, fill=color,
                         text_anchor=anchor, font_weight=weight))
    return line, box, txt

# ==================== DIAGRAM 2: THE CASCADE ====================
d = dw.Drawing(1660, 600, origin=(0, 0))
d.append(dw.Rectangle(0, 0, 1660, 600, fill='white'))
MK = mk(d); line, box, txt = helpers(d, MK)

def storey(x, label, sub, cands):
    box(x, 120, 360, 170, BLUEBG, BLUE)
    txt(label, x+180, 145, 16, BLUE, weight='bold')
    txt(sub, x+180, 165, 11.5, GREY)
    for i, c in enumerate(cands):
        box(x+22+i*112, 180, 100, 34, 'white', BLUE, rx=7, sw=1.2)
        txt(c, x+72+i*112, 201, 11.5, INK)
    for i, b in enumerate(['characterization', 'geometry', 'query calculus']):
        box(x+22+i*112, 232, 100, 26, GREENBG, GREEN, rx=13, sw=1.2)
        txt(b, x+72+i*112, 249, 9.5, GREEN)
    txt('the same three law cards, stamped at this storey', x+180, 278, 10, GREY)

storey(40,  'STOREY 0 · the model store', 'decode D · candidates are models', ['model c1', 'model c2', 'model c3'])
storey(650, 'STOREY 1 · metaprograms over c0', 'decode = apply to c0, then run', ['modifier e0', 'modifier e1', 'modifier e2'])
storey(1260, 'STOREY 2 · and so on', 'decode = apply to e, then run', ['modifier f0', 'modifier f1', '…'])

for x, lbl in [(400, 'ACCEPT c0'), (1010, 'ACCEPT e')]:
    line(x+2, 205, x+248, 205, INK, 2.6)
    box(x+70, 186, 116, 38, 'white', INK, rx=19)
    txt(lbl, x+128, 205, 12.5, INK, weight='bold')
    txt('a capacity write', x+128, 218, 9.5, GREY)

# flat plane
box(40, 340, 1580, 64, LGREY, GREY, rx=10)
txt('COLLAPSE AT COMPUTATION:  a storey over a storey is one storey at the composed application  ·  anchored(anchored(D, f), g) = anchored(D, f ∘ g)  ·  one machine, definitionally',
    830, 368, 13, INK)
txt('the loop of retrieve, accept, retrieve is algebraically a single store', 830, 388, 11, GREY)
for x in [220, 830, 1440]:
    line(x, 292, x, 340, GREY, 1.6, dash='5,4')

# certificate chain
box(40, 434, 1580, 120, 'white', AMBER, rx=10)
txt('STACKING AT CERTIFICATION:  the certificate chain', 830, 458, 13.5, AMBER, weight='bold')
cx = 120
for lbl, cond in [('certificate 0', 'model c0 fits the evidence; c0 is the least survivor'),
                  ('certificate 1 | c0', 'modifier e fits the spec words at c0; e least survivor'),
                  ('certificate 2 | c0, e', 'and so on, each conditional on every accept below')]:
    box(cx, 472, 420, 62, AMBERBG, AMBER, rx=8, sw=1.2)
    txt(lbl, cx+210, 494, 12.5, AMBER, weight='bold')
    txt(cond, cx+210, 514, 10.5, INK)
    if cx < 900: line(cx+424, 503, cx+486, 503, AMBER, 2.2)
    cx += 490
txt('grandfathering: an accepted anchor survives new evidence exactly while its index survives, and everything above it stands  ·  drift budget: at most one anchor revision per distinct model held',
    830, 578, 11, GREY)
txt('guard: modifier stores must be codes as data; unrestricted modifier families saturate in one step', 830, 594, 10, RED)

d.save_svg('/Users/polaris/Documents/Epistemology and Zetesis/Projects/transformer-learning-theory/machine_card/machine_cascade.svg')

# ==================== DIAGRAM 3: THE WITNESS ====================
d = dw.Drawing(1660, 780, origin=(0, 0))
d.append(dw.Rectangle(0, 0, 1660, 780, fill='white'))
MK = mk(d); line, box, txt = helpers(d, MK)

def zone(x, w, label, color):
    d.append(dw.Rectangle(x, 12, w, 28, rx=14, fill=color, opacity=0.14))
    txt(label, x+w/2, 31, 15, color, weight='bold')

zone(20, 540, 'STOREY 0 · retrieve the mechanism', BLUE)
zone(580, 500, 'ACCEPT · retrieve the surgery', AMBER)
zone(1100, 540, 'THE THIRD RUNG · the twin word', RED)

def table(x, y, cols, rows, cw, ch, header_color, kill=None, hi_cols=None):
    txt('', x, y)
    for j, cn in enumerate(cols):
        txt(cn, x+cw+j*cw+cw/2, y-6, 10.5, header_color, weight='bold')
    for i, (rn, vals) in enumerate(rows):
        ry = y + i*ch
        txt(rn, x+cw/2, ry+ch/2+4, 11, INK, weight='bold')
        for j, v in enumerate(vals):
            fill = 'white'
            if kill and (i, j) in kill: fill = REDBG
            if hi_cols and j in hi_cols: fill = GREENBG
            box(x+cw+j*cw, ry, cw, ch, fill, GREY, rx=3, sw=0.9)
            txt(str(v), x+cw+j*cw+cw/2, ry+ch/2+4, 10.5, RED if (kill and (i, j) in kill) else INK)

# --- Zone A: base store ---
txt('decode table (kernel values)', 290, 66, 11, GREY)
table(40, 84, ['read X', 'read Y', 'doX1·Y', 'doY1·X'],
      [('M1: X→Y', [0, 0, 1, 0]), ('M2: Y→X', [0, 0, 0, 1]), ('M3: common', [0, 0, 0, 0])],
      90, 30, BLUE, kill={(0, 2), (1, 3)})
y0 = 200
steps = [('words (readX,0),(readY,0)', '{M1, M2, M3}', 'all rows read 0 on both', INK),
         ('+ word (doX1·Y, 0)', '{M2, M3}', 'kills M1: its cell reads 1 ≠ 0', RED),
         ('query answered: survivors agree on doX1·Y = 0   (price 1, two survivors)', '', '', GREEN),
         ('+ word (doY1·X, 0)', '{M3}', 'kills M2: its cell reads 1 ≠ 0', RED),
         ('identified: M3   (price 2)', '', '', GREEN)]
for i, (lbl, mask, why, c) in enumerate(steps):
    sy = y0 + i*62
    if mask:
        box(40, sy, 300, 46, 'white', c if c != INK else GREY, rx=7, sw=1.3)
        txt(lbl, 190, sy+19, 11, INK)
        txt(why, 190, sy+36, 9.5, GREY)
        box(360, sy+4, 180, 38, BLUEBG, BLUE, rx=7, sw=1.2)
        txt(mask, 450, sy+27, 12.5, BLUE, weight='bold')
        if i < 4: line(190, sy+46, 190, sy+62, INK, 1.8)
    else:
        box(40, sy, 500, 40, GREENBG, GREEN, rx=7, sw=1.3)
        txt(lbl, 290, sy+24, 11.5, GREEN, weight='bold')
        if i < 4: line(190, sy+40, 190, sy+62, INK, 1.8)

# --- Zone B: anchored store ---
line(544, 480, 592, 300, AMBER, 2.6)
box(596, 258, 200, 40, 'white', INK, rx=20)
txt('anchor := M3', 696, 276, 12.5, INK, weight='bold')
txt('(accepted; a capacity write)', 696, 291, 9.5, GREY)
txt('surgery store at M3 (kernel values)', 830, 330, 11, GREY)
table(600, 348, ['read X', 'read Y'],
      [('e0 = do X:=1', [1, 0]), ('e1 = do Y:=1', [0, 1])],
      110, 30, AMBER, kill={(1, 0)})
box(600, 420, 460, 44, TEALBG, TEAL, rx=7)
txt('specification (the tagged semantics of do X:=1):  X reads 1,  Y reads 0', 830, 438, 11, TEAL)
txt('coherence words fed as evidence:  (readX, 1), (readY, 0)', 830, 455, 10.5, GREY)
box(600, 480, 460, 46, 'white', RED, rx=7, sw=1.3)
txt('(readX, 1) kills e1: its cell reads 0 ≠ 1', 830, 499, 11, RED)
txt('survivors {e0}  →  retrieved: e0 = the do X:=1 surgery', 830, 516, 11, INK, weight='bold')
box(600, 542, 460, 60, AMBERBG, AMBER, rx=8)
txt('THE CHAINED CERTIFICATE', 830, 562, 12, AMBER, weight='bold')
txt('M3 fits the evidence  ∧  e0 fits the spec words at M3', 830, 580, 10.5, INK)
txt('and each is its stage’s least survivor: the freeze is certified', 830, 595, 10.5, INK)

# --- Zone C: third rung ---
txt('response sets over the shared seed u (kernel values)', 1370, 66, 11, GREY)
table(1110, 84, ['[do X:=0]', '[do X:=1]', 'twin [0,1]'],
      [('coupled', ['{0},{1}', '{0},{1}', '{00},{11}']),
       ('anti', ['{0},{1}', '{1},{0}', '{01},{10}'])],
      120, 30, RED, hi_cols={0, 1})
txt('single-regime columns: EQUAL as sets — indistinguishable', 1370, 162, 10.5, GREEN)
txt('twin column: DIFFERENT — the separator', 1370, 178, 10.5, RED)
box(1110, 200, 500, 88, 'white', GREY, rx=8)
txt('every single-regime word keeps both mechanisms alive:', 1360, 222, 11, INK)
txt('indistinguishable across every per-regime intervention', 1360, 239, 11, INK)
txt('(the banked indistinguishability (dark-pair) laws apply to this pair verbatim:', 1360, 258, 9.5, GREY)
txt('co-survival on every sample, blindness at the limit)', 1360, 272, 9.5, GREY)
box(1110, 304, 500, 76, REDBG, RED, rx=8)
txt('buy the TWIN word: ([doX0, doX1], {00, 11})', 1360, 326, 11.5, RED, weight='bold')
txt('one seed bound across two regimes: the counterfactual question', 1360, 344, 10, INK)
txt('anti is killed; survivors {coupled}: the third rung, separated', 1360, 362, 10.5, INK, weight='bold')
box(1110, 396, 500, 70, GREENBG, GREEN, rx=8)
txt('answered after the twin, unanswered before it:', 1360, 418, 11, GREEN)
txt('the cross-regime read is constant on {coupled} and was not', 1360, 436, 10, INK)
txt('constant on {coupled, anti}: answered before identified, rung three', 1360, 453, 10, INK)
txt('L1  ⊊  L2  ⊊  L3,  executed:', 1360, 500, 12.5, INK, weight='bold')
txt('observation cannot separate what intervention can;', 1360, 520, 10.5, GREY)
txt('per-regime intervention cannot separate what one twin word can', 1360, 536, 10.5, GREY)

# footer
d.append(dw.Line(20, 700, 1640, 700, stroke=INK, stroke_width=1.2))
txt('Every table cell and every survivor-set transition above is evaluated inside the proof checker; the figure exhibits the proof.', 830, 726, 12, INK)
txt('scm_cycle_base · scm_cycle_anchored · scm_cycle_certified · scmL3_interventional_dark · scmL3_twin_separates · scmL3_twin_answers', 830, 748, 10, GREY)
txt('(the first three and the collapse are axiom-free or propositional-extensionality only)', 830, 764, 9.5, GREY)

d.save_svg('/Users/polaris/Documents/Epistemology and Zetesis/Projects/transformer-learning-theory/machine_card/machine_witness.svg')
print('SVGS OK')
