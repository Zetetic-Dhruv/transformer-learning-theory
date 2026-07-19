#!/usr/bin/env python3
"""The Model Store machine diagram: input / processing / output, structurally."""
import drawsvg as dw

W, H = 1660, 700
d = dw.Drawing(W, H, origin=(0, 0))
d.append(dw.Rectangle(0, 0, W, H, fill='white'))

INK = '#22223b'; GREY = '#8a8fa3'; LGREY = '#e7e9f0'
TEAL = '#0f766e'; TEALBG = '#e9f5f3'
BLUE = '#1d4ed8'; BLUEBG = '#eaf0fd'
AMBER = '#b45309'; AMBERBG = '#fdf3e7'
RED = '#b91c1c'; GREEN = '#15803d'
F = 'Helvetica'

def arrow_marker(color, mid):
    m = dw.Marker(-0.1, -5, 10, 5, scale=1, orient='auto', id=mid)
    m.append(dw.Lines(-0.1, -4, 9, 0, -0.1, 4, close=True, fill=color))
    d.append(m)
    return m

MK = {c: arrow_marker(c, f'ah{i}') for i, c in enumerate([INK, TEAL, BLUE, AMBER, RED, GREY, GREEN])}

def line(x1, y1, x2, y2, color=INK, w=2.0, dash=None, arrow=True):
    kw = dict(stroke=color, stroke_width=w, fill='none')
    if dash: kw['stroke_dasharray'] = dash
    if arrow: kw['marker_end'] = MK[color]
    d.append(dw.Line(x1, y1, x2, y2, **kw))

def box(x, y, w, h, fill, stroke, rx=9, sw=1.6):
    d.append(dw.Rectangle(x, y, w, h, rx=rx, fill=fill, stroke=stroke, stroke_width=sw))

def txt(s, x, y, size=15, color=INK, anchor='middle', weight='normal', style=None):
    kw = dict(font_size=size, font_family=F, fill=color, text_anchor=anchor, font_weight=weight)
    if style: kw['font_style'] = style
    d.append(dw.Text(s, x=x, y=y, **kw))

# ============ ZONE HEADERS ============
def zone(x, w, label, color):
    d.append(dw.Rectangle(x, 14, w, 30, rx=15, fill=color, opacity=0.14))
    txt(label, x + w/2, 35, 17, color, weight='bold')

zone(18, 360, 'INPUT  ·  assembly of words', TEAL)
zone(400, 700, 'PROCESSING  ·  the version space', BLUE)
zone(1122, 520, 'OUTPUT  ·  certificate and reads', AMBER)

# ============ INPUT ============
# live evidence stream
box(30, 70, 330, 84, TEALBG, TEAL)
txt('live context  s', 195, 92, 15, TEAL, weight='bold')
wx = 52
for lbl, tag in [('(x₁,y₁)', 'obs'), ('(x₂,y₂)', 'do'), ('(x₃,y₃)', '+/-')]:
    box(wx, 104, 88, 36, 'white', TEAL, rx=7, sw=1.2)
    txt(lbl, wx+44, 124, 13.5, INK)
    box(wx+22, 96, 44, 15, TEAL, TEAL, rx=7)
    txt(tag, wx+44, 107.5, 10, 'white')
    wx += 102
txt('tags are alphabet content: observational, interventional, negated', 195, 168, 11.5, GREY)

# capacity memory
box(30, 196, 330, 92, TEALBG, TEAL)
txt('capacity memory   mem : key → stored trace', 195, 218, 14.5, TEAL, weight='bold')
box(52, 230, 130, 40, 'white', TEAL, rx=7, sw=1.2)
txt('ℓ ↦ [(x,y),…]', 117, 253, 13, INK)
box(200, 230, 138, 40, 'white', TEAL, rx=7, sw=1.2)
txt('a label is a', 269, 245, 11.5, GREY)
txt('pre-purchased experiment', 269, 260, 11.5, GREY)

# assembly join
box(150, 316, 120, 44, 'white', INK, rx=22)
txt('assemble', 210, 334, 14, INK, weight='bold')
txt('s ++ mem ℓ', 210, 351, 12.5, GREY)
line(195, 154, 205, 316, TEAL, 2.2)
line(195, 288, 205, 316, TEAL, 2.2)
line(270, 338, 400, 338, INK, 2.6)
txt('the interface never grows: a list of words in', 210, 386, 11.5, GREY)

# ============ PROCESSING ============
# two rails
box(420, 64, 300, 46, BLUEBG, BLUE, rx=8)
txt('threaded automaton (sequential state)', 570, 84, 13.5, BLUE)
txt('reads order', 570, 100, 11, GREY)
box(760, 64, 300, 46, BLUEBG, BLUE, rx=8)
txt('order-free pool (commutative merge)', 910, 84, 13.5, BLUE)
txt('order-blind', 910, 100, 11, GREY)
txt('=', 740, 92, 22, BLUE, weight='bold')
txt('one function, two machines', 740, 130, 12, BLUE)

# funnel: nested survivor columns
fx = [470, 620, 770, 920]; fy = 200; dotr = 8.5
alive = [[1,1,1,1,1], [1,0,1,1,1], [1,0,1,0,1], [0,0,1,0,1]]
for col in range(4):
    n_alive = sum(alive[col])
    box(fx[col]-34, fy-28, 68, 200, 'white', BLUE, rx=12, sw=1.8)
    txt(f'V{chr(0x2080+col)}', fx[col], fy-38, 13.5, BLUE, weight='bold')
    for row in range(5):
        cy = fy + row*38
        if alive[col][row]:
            d.append(dw.Circle(fx[col], cy, dotr, fill=BLUE))
        else:
            d.append(dw.Circle(fx[col], cy, dotr, fill='white', stroke=GREY, stroke_width=1.6))
            d.append(dw.Line(fx[col]-5, cy-5, fx[col]+5, cy+5, stroke=RED, stroke_width=1.8))
for col in range(3):
    line(fx[col]+40, fy+66, fx[col+1]-42, fy+66, INK, 2.4)
    txt(f'w{chr(0x2081+col)}', (fx[col]+fx[col+1])/2, fy+56, 13, INK)
    txt('keep-filter', (fx[col]+fx[col+1])/2, fy+84, 10, GREY)
txt('candidates only leave, never return:  V₀ ⊇ V₁ ⊇ V₂ ⊇ V₃', 695, fy+206, 12.5, BLUE)

# white-box decodes from rails to funnel
for col in range(4):
    line(fx[col], 112, fx[col], fy-42, GREY, 1.6, dash='5,4')
txt('every internal state decodes, certified, to the survivor set (white box)', 740, 152, 12, GREY)

# support / weights strata
box(420, 458, 640, 58, LGREY, GREY, rx=9)
txt('SUPPORT: which candidates survive     |     WEIGHTS: scores and margins', 740, 481, 12.5, INK)
txt('the hard channel reads support only; tempering and training move weights only', 740, 501, 11.5, GREY)
line(695, 428, 695, 458, GREY, 1.6, dash='4,4')

# assembly to funnel
line(400, 338, 436, 300, INK, 2.6)

# ============ OUTPUT ============
# certificate
box(1140, 70, 210, 120, AMBERBG, AMBER)
txt('certificate', 1245, 92, 15, AMBER, weight='bold')
txt('V(s) itself is output:', 1245, 112, 11.5, GREY)
for i, cy in enumerate([132, 156]):
    d.append(dw.Circle(1215 + i*0, cy, 0, fill='none'))
d.append(dw.Circle(1220, 140, 8, fill=BLUE))
d.append(dw.Circle(1250, 140, 8, fill=BLUE))
d.append(dw.Circle(1280, 140, 8, fill='white', stroke=GREY, stroke_width=1.5))
txt('checkable by anyone', 1245, 172, 11.5, GREY)
line(960, 266, 1140, 140, AMBER, 2.4)

# selection head
box(1400, 70, 230, 120, AMBERBG, AMBER)
txt('selection head', 1515, 92, 15, AMBER, weight='bold')
txt('least surviving index', 1515, 113, 12.5, INK)
txt('some c   |   none', 1515, 133, 13.5, INK, weight='bold')
txt('Occam optimum; softmax top-1', 1515, 155, 11, GREY)
txt('at every temperature', 1515, 169, 11, GREY)
line(1350, 130, 1400, 130, AMBER, 2.2)

# reads fan-out
box(1140, 220, 490, 108, 'white', AMBER, rx=10)
txt('reads: functionals of the certificate', 1385, 242, 13.5, AMBER, weight='bold')
for bx, t1, t2 in [(1160, 'exists?', 'flips ≤ once'),
                   (1282, 'count', 'one drop per death'),
                   (1404, 'answer q', 'answered iff'),]:
    box(bx, 254, 108, 58, LGREY, GREY, rx=7, sw=1.2)
    txt(t1, bx+54, 276, 12.5, INK, weight='bold')
    txt(t2, bx+54, 293, 10.5, GREY)
txt('survivors agree', 1458, 305, 10.5, GREY)
box(1526, 254, 92, 58, LGREY, GREY, rx=7, sw=1.2)
txt('select', 1572, 276, 12.5, INK, weight='bold')
txt('≤ #models', 1572, 293, 10.5, GREY)
txt('revisions', 1572, 305, 10.5, GREY)

# answered before identified inset
box(1140, 352, 490, 92, 'white', GREEN, rx=10, sw=1.6)
txt('answered before identified', 1385, 374, 13.5, GREEN, weight='bold')
d.append(dw.Circle(1210, 405, 9, fill=BLUE)); txt('M₂', 1210, 430, 11, INK)
d.append(dw.Circle(1250, 405, 9, fill=BLUE)); txt('M₃', 1250, 430, 11, INK)
txt('↦  same answer  ⇒  query certified', 1420, 402, 12.5, INK)
txt('two survivors  ⇒  model still unknown', 1420, 424, 11.5, GREY)

# causal inset
box(1140, 466, 490, 108, 'white', RED, rx=10, sw=1.6)
txt('causal words: the smallest honest witness', 1385, 488, 13, RED, weight='bold')
d.append(dw.Ellipse(1230, 528, 78, 30, fill='none', stroke=GREY, stroke_width=1.5, stroke_dasharray='5,4'))
for mx, ml in [(1180, 'X→Y'), (1230, 'Y→X'), (1280, 'U')]:
    d.append(dw.Circle(mx, 528, 10, fill='white', stroke=INK, stroke_width=1.6))
    txt(ml, mx, 556, 10, INK)
txt('dark under observation', 1230, 505, 10, GREY)
line(1318, 528, 1372, 528, RED, 2.2)
txt('do X:=1', 1345, 518, 11, RED)
txt('query answered: 1 word', 1500, 515, 12, INK)
txt('model identified: 2 words', 1500, 534, 12, INK)
txt('from memory: 0 words', 1500, 553, 12, GREEN, weight='bold')

# ============ TIMELINE BAND ============
ty = 636
line(60, ty, 1600, ty, INK, 2.4)
txt('the run, in time', 60, ty-30, 12.5, INK, anchor='start', weight='bold')
ticks = [(180, 'revision 1'), (330, 'revision 2'), (480, f'… ≤ #models total')]
for tx_, tl in ticks:
    d.append(dw.Line(tx_, ty-9, tx_, ty+9, stroke=INK, stroke_width=2))
    txt(tl, tx_, ty+28, 11, GREY)
d.append(dw.Line(700, ty-12, 700, ty+12, stroke=RED, stroke_width=3))
txt('falsified ⇒ forever', 700, ty+28, 11, RED)
txt('(one-way door)', 700, ty-18, 10, RED)
d.append(dw.Line(1000, ty-12, 1000, ty+12, stroke=GREEN, stroke_width=3))
txt('settling time N: every dial freezes at once', 1000, ty+28, 11, GREEN)
d.append(dw.Circle(1430, ty, 7, fill=INK))
txt('limit decode', 1430, ty+28, 11, INK)
txt('fixed by no finite prefix; captured by one ⋃⋂ of finite events', 1430, ty-18, 10.5, GREY)

d.save_svg('/Users/polaris/Documents/Epistemology and Zetesis/Projects/transformer-learning-theory/machine_card/machine_diagram.svg')
print('SVG OK')
