"""Exact-arithmetic model of SQLite's REAL rendering (%!.17g, sqlite3FpDecode),
checked against the native build: experiments/real/spec.py < build/render.txt"""
import sys, struct
from fractions import Fraction

def to_double(bits):
    return struct.unpack('<d', struct.pack('<Q', bits))[0]

def exact(bits):
    neg = bits >> 63; e = (bits >> 52) & 0x7ff; f = bits & ((1 << 52) - 1)
    if e == 0: m, ex = f, -1074
    else: m, ex = f | (1 << 52), e - 1075
    return neg, Fraction(m) * (Fraction(2) ** ex)

def nearest_double(fr):
    """correctly rounded (ties to even) double of a positive fraction"""
    return float(fr)   # Python's Fraction.__float__ is correctly rounded

def digits(F, n, mode):
    """(d, exp) with d having n digits (or n+1 after carry), F ~ d*10^exp"""
    k = 0
    # find exponent so that 10^(n-1) <= F/10^k < 10^n
    import math
    k = math.floor(math.log10(F)) - (n - 1)
    while F / Fraction(10) ** k >= 10 ** n: k += 1
    while F / Fraction(10) ** k < 10 ** (n - 1): k -= 1
    q = F / Fraction(10) ** k
    fl = q.numerator // q.denominator
    rem = q - fl
    if mode == 'even':
        if rem > Fraction(1, 2) or (rem == Fraction(1, 2) and fl % 2 == 1): fl += 1
    elif mode == 'floor':
        pass
    elif mode == 'up':
        if rem >= Fraction(1, 2): fl += 1
    return fl, k

def pwr2to10(x): return (x * 78913) >> 18
def pwr10to2(x): return (x * 108853) >> 15

def sqlite_digits(bits):
    """sqlite3Fp2Convert10(m, e, 18): the decimal scale p comes from the
    estimate pwr2to10, so the result has 18 or 19 digits; the digits are
    X = m*2^e*10^p rounded half up (h = floor(2X), D = (h+1)>>1 when h is odd)"""
    e = (bits >> 52) & 0x7ff; v = bits & ((1 << 52) - 1)
    if e == 0:
        nn = 64 - v.bit_length(); v <<= nn; e = -1074 - nn
    else:
        v = (v << 11) | (1 << 63); e -= 1086
    p = 18 - 1 - pwr2to10(e + 63)
    L = pwr10to2(p)
    t = Fraction(10) ** p * Fraction(2) ** (63 - L)
    x = t.numerator // t.denominator           # 10^p as a 64-bit fraction, truncated
    h = (v * x) >> 64                           # sqlite3Multiply128, high word
    h >>= -(e + L + 2)
    return (h + ((h << 1) & 2)) >> 1, -p

def render(bits, mode):
    neg, F = exact(bits)
    if F == 0: return '0.0'
    r = to_double(bits)
    if mode == 'sqlite': v, exp = sqlite_digits(bits)
    else: v, exp = digits(F, 18, mode)
    z = list(str(v)); n = len(z); iDP = n + exp
    iRound = 17
    if iRound < n:
        if z[15] == '9' and z[14] == '9':
            jj = 14
            while jj > 0 and z[jj - 1] == '9': jj -= 1
            v2 = 1 if jj == 0 else int(''.join(z[:jj])) + 1
            if abs(r) == nearest_double(Fraction(v2) * Fraction(10) ** (exp + n - jj)): iRound = jj + 1
        elif iDP >= n or (z[15] == '0' and z[14] == '0' and z[13] == '0'):
            jj = 13
            while z[jj - 1] == '0': jj -= 1
            v2 = int(''.join(z[:jj]))
            if abs(r) == nearest_double(Fraction(v2) * Fraction(10) ** (exp + n - jj)): iRound = jj + 1
        nd = iRound
        if z[iRound] >= '5':
            j = iRound - 1
            while True:
                z[j] = chr(ord(z[j]) + 1)
                if z[j] <= '9': break
                z[j] = '0'
                if j == 0:
                    z.insert(0, '1'); nd += 1; iDP += 1; break
                j -= 1
        z = z[:nd]
    while z[-1] == '0': z.pop()
    e10 = iDP - 1
    ds = ''.join(z)
    sign = '-' if neg else ''
    if e10 < -4 or e10 >= 17:
        mant = ds[0] + '.' + (ds[1:] if len(ds) > 1 else '0')
        return f"{sign}{mant}e{'-' if e10 < 0 else '+'}{abs(e10):02d}"
    if iDP <= 0:
        return sign + '0.' + '0' * (-iDP) + ds
    if iDP >= len(ds):
        return sign + ds + '0' * (iDP - len(ds)) + '.0'
    return sign + ds[:iDP] + '.' + ds[iDP:]

mode = sys.argv[1] if len(sys.argv) > 1 else 'even'
bad = 0; tot = 0
for line in sys.stdin:
    h, want = line.split()
    got = render(int(h, 16), mode)
    tot += 1
    if got != want:
        bad += 1
        if bad <= 5: print('MISMATCH', h, want, got)
print(f'{tot} values, {bad} mismatches ({mode})')
