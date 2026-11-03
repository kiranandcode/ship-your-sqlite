"""pow10.py < pow10.out: is powerOfTen(p) the truncated top 64 bits of 10^p?"""
import sys
from fractions import Fraction
bad = 0
for line in sys.stdin:
    p, h, lo = map(int, line.split())
    L = (p * 108853) >> 15
    v = Fraction(10) ** p * Fraction(2) ** (63 - L)
    fl = v.numerator // v.denominator
    if h != fl:
        bad += 1
        print('diff', p, h - fl)
print('bad', bad)
