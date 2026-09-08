module type.type;

import std.stdio;
import std.conv;
import std.string;
import std.math;
import std.algorithm;
import std.exception;
import std.traits;
import std.bigint;
import std.format;

// Helper to extract double value
double getDouble(T)(T v) {
    alias UT = Unqual!T;
    static if (isNumeric!UT) return to!double(v);
    else static if (is(UT == fra)) return to!double(v.num) / to!double(v.den);
    else static if (is(UT == dfloat)) return v.val;
    else static if (is(UT == dec)) return v.val;
    else static if (is(UT == posit)) return v.val;
    else static if (is(UT == bid) || is(UT == dpd)) return to!double(v.toString());
    else return 0.0;
}

// Helper to convert to fraction
fra getFra(T)(T v) {
    alias UT = Unqual!T;
    static if (is(UT == fra)) {
        return v;
    } else static if (is(UT == bid)) {
        return fra.exactFrom(v);
    } else static if (is(UT == dpd)) {
        return fra.exactFrom(v.toBid());
    } else {
        // Very basic float to fraction conversion by multiplying by 1000000
        double d = getDouble(v);
        long den = 1000000;
        long num = cast(long)(d * den);
        return simfra(fra(num, den));
    }
}

// 1. gcd, lcm
long gcd(long a, long b) {
    while (b != 0) {
        long temp = b;
        b = a % b;
        a = temp;
    }
    return a > 0 ? a : -a;
}

long lcm(long a, long b) {
    if (a == 0 || b == 0) return 0;
    long res = (a / gcd(a, b)) * b;
    return res > 0 ? res : -res;
}

BigInt bigGcd(BigInt a, BigInt b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        BigInt t = b;
        b = a % b;
        a = t;
    }
    return a;
}

// 2. fra (Fraction)
struct fra {
    long num;
    long den;
    
    this(long numerator, long denominator) {
        enforce(denominator != 0, "Denominator cannot be zero");
        num = numerator;
        den = denominator;
    }

    // Enables direct declaration from an integer literal: fra x = 5;
    this(long v) {
        num = v;
        den = 1;
    }

    // Enables direct declaration from a string: fra x = "3/4"; or fra x = "0.75";
    this(string s) {
        auto slashPos = s.indexOf('/');
        if (slashPos != -1) {
            num = to!long(s[0 .. slashPos]);
            den = to!long(s[slashPos + 1 .. $]);
            enforce(den != 0, "Denominator cannot be zero");
        } else {
            fra exact = exactFrom(bid(s));
            num = exact.num;
            den = exact.den;
        }
    }

    // Exact (lossless) conversion from a bid value: coefficient * 10^exponent
    // is reduced to num/den, so e.g. 0.25 becomes exactly 1/4, not an
    // approximation. Throws if the reduced value overflows `long`.
    static fra exactFrom(bid b) {
        BigInt n, d;
        if (b.exponent >= 0) {
            n = b.coefficient * pow10(b.exponent);
            d = BigInt(1);
        } else {
            n = b.coefficient;
            d = pow10(-b.exponent);
        }
        BigInt g = bigGcd(n, d);
        if (g != 0) { n /= g; d /= g; }
        enforce(n <= long.max && d <= long.max,
                "Value too large to represent exactly as fra (long overflow)");
        long ln = n.toLong();
        long ld = d.toLong();
        return fra(b.negative ? -ln : ln, ld);
    }

    string toString() const {
        return to!string(num) ~ "/" ~ to!string(den);
    }

    fra opBinary(string op, R)(R rhs) const {
        fra r = getFra(rhs);
        fra l = this;
        static if (op == "+") {
            long d = lcm(l.den, r.den);
            return simfra(fra(l.num * (d / l.den) + r.num * (d / r.den), d));
        } else static if (op == "-") {
            long d = lcm(l.den, r.den);
            return simfra(fra(l.num * (d / l.den) - r.num * (d / r.den), d));
        } else static if (op == "*") {
            return simfra(fra(l.num * r.num, l.den * r.den));
        } else static if (op == "/") {
            return simfra(fra(l.num * r.den, l.den * r.num));
        } else {
            static assert(0, "Operator not supported");
        }
    }
}

fra simfra(fra f) {
    long d = gcd(f.num, f.den);
    long newNum = f.num / d;
    long newDen = f.den / d;
    if (newDen < 0) {
        newNum = -newNum;
        newDen = -newDen;
    }
    return fra(newNum, newDen);
}

void comden(ref fra a, ref fra b) {
    long d = lcm(a.den, b.den);
    a.num *= (d / a.den);
    b.num *= (d / b.den);
    a.den = d;
    b.den = d;
}

// 3. dfloat
struct dfloat {
    double val;
    long precisionBytes = 8;
    
    this(double v) {
        val = v;
    }
    
    string toString() const {
        return to!string(val);
    }

    auto opBinary(string op, R)(R rhs) const {
        static if (is(Unqual!R == fra)) {
            return getFra(this).opBinary!op(rhs);
        } else {
            double r = getDouble(rhs);
            mixin("return dfloat(val " ~ op ~ " r);");
        }
    }
}

// 4. dec
struct dec {
    string mode;
    double val;
    
    this(double v, string m = "dpd") {
        val = v;
        mode = m;
    }
    
    string toString() const {
        return to!string(val) ~ "(" ~ mode ~ ")";
    }

    auto opBinary(string op, R)(R rhs) const {
        static if (is(Unqual!R == fra)) {
            return getFra(this).opBinary!op(rhs);
        } else static if (is(Unqual!R == dfloat)) {
            return dfloat(this.val).opBinary!op(rhs); // Prioritize dfloat
        } else {
            double r = getDouble(rhs);
            mixin("return dec(val " ~ op ~ " r, mode);");
        }
    }
}

// 5. posit
struct posit {
    int bits;
    double val;
    
    this(double v, int b = 32) {
        val = v;
        bits = b;
    }
    
    string toString() const {
        return "posit" ~ to!string(bits) ~ ":" ~ to!string(val);
    }

    auto opBinary(string op, R)(R rhs) const {
         static if (is(Unqual!R == fra)) {
            return getFra(this).opBinary!op(rhs);
        } else static if (is(Unqual!R == dfloat) || is(Unqual!R == dec)) {
            // Prioritize higher precision / dfloat
            double r = getDouble(rhs);
            mixin("return dfloat(val " ~ op ~ " r);");
        } else {
            double r = getDouble(rhs);
            mixin("return posit(val " ~ op ~ " r, bits);");
        }
    }
}

// 6. solve

// Parses one side of an equation into coefficients indexed by power,
// so "2x^2 - 3x + 1" becomes [1, -3, 2, 0]. Accepts an implicit 1
// coefficient ("x^2"), an optional '*' ("2*x"), and free whitespace.
// Coefficients are kept as exact bid values, never routed through a
// double, so the arbitrary-precision solver starts from exact input.
private bid[4] parseSide(string expr, char varName) {
    import std.ascii : isAsciiDigit = isDigit;

    bid[4] coeffs = [bid(0L), bid(0L), bid(0L), bid(0L)];
    size_t i = 0;

    void skipSpaces() {
        while (i < expr.length && (expr[i] == ' ' || expr[i] == '\t')) i++;
    }

    skipSpaces();
    enforce(i < expr.length, "Empty expression in equation");

    while (i < expr.length) {
        skipSpaces();
        if (i >= expr.length) break;

        bool negate = false;
        if (expr[i] == '+') { i++; }
        else if (expr[i] == '-') { negate = true; i++; }
        skipSpaces();

        // Coefficient, if written out.
        bid coeff = bid(1L);
        bool hasCoeff = false;
        size_t start = i;
        while (i < expr.length && (isAsciiDigit(expr[i]) || expr[i] == '.')) i++;
        if (i > start) {
            coeff = bid(expr[start .. i].idup);
            hasCoeff = true;
        }

        skipSpaces();
        if (i < expr.length && expr[i] == '*') { i++; skipSpaces(); }

        // Variable and its power, if present.
        int power = 0;
        if (i < expr.length && expr[i] == varName) {
            i++;
            power = 1;
            skipSpaces();
            if (i < expr.length && expr[i] == '^') {
                i++;
                skipSpaces();
                start = i;
                while (i < expr.length && isAsciiDigit(expr[i])) i++;
                enforce(i > start, "Missing exponent after '^'");
                power = to!int(expr[start .. i]);
            }
        } else {
            enforce(hasCoeff, "Unexpected character in equation: '" ~ expr[i] ~ "'");
        }

        enforce(power <= 3, "Only equations up to degree 3 are supported");
        if (negate) coeff.negative = !coeff.negative && coeff.coefficient != 0;
        coeffs[power] = coeffs[power] + coeff;
        skipSpaces();
    }

    return coeffs;
}

// Trims float noise so roots read as "2" rather than "1.9999999999999998".
private string formatRoot(double v) {
    double rounded = std.math.round(v);
    if (abs(v - rounded) < 1e-9) v = rounded;
    if (v == 0) v = 0.0; // collapse -0
    return format("%.10g", v);
}

private string formatComplex(double re, double im) {
    if (abs(im) < 1e-9) return formatRoot(re);
    string sign = im < 0 ? " - " : " + ";
    return formatRoot(re) ~ sign ~ formatRoot(abs(im)) ~ "i";
}

// Reduces an equation to exact coefficients indexed by power, moving any
// right-hand terms across the '='. Shared by both solvers.
private bid[4] equationCoeffs(string equation, char v) {
    auto eqPos = equation.indexOf('=');
    bid[4] coeffs = parseSide(eqPos == -1 ? equation : equation[0 .. eqPos], v);
    if (eqPos != -1) {
        bid[4] rhs = parseSide(equation[eqPos + 1 .. $], v);
        foreach (idx; 0 .. 4) coeffs[idx] = coeffs[idx] - rhs[idx];
    }
    return coeffs;
}

// Solves a polynomial equation of degree 1-3 in one variable.
// `varName` is the variable to solve for ("x" if empty); `equation` may
// carry terms on both sides ("x^2 = 2x + 3") or none on the right.
// Returns one "<var>: <root>" entry per root, complex roots included.
// Roots are computed in double precision; see solvePrecise for exact work.
string[] solve(string varName, string equation) {
    char v = varName.length ? varName[0] : 'x';

    bid[4] exact = equationCoeffs(equation, v);
    double[4] coeffs;
    foreach (idx; 0 .. 4) coeffs[idx] = getDouble(exact[idx]);

    enum eps = 1e-12;
    string label(string root) { return v ~ ": " ~ root; }

    double a3 = coeffs[3], a2 = coeffs[2], a1 = coeffs[1], a0 = coeffs[0];

    if (abs(a3) < eps && abs(a2) < eps && abs(a1) < eps) {
        return abs(a0) < eps ? ["infinitely many solutions"] : ["no solution"];
    }

    if (abs(a3) < eps && abs(a2) < eps) {
        return [label(formatRoot(-a0 / a1))];
    }

    if (abs(a3) < eps) {
        double disc = a1 * a1 - 4 * a2 * a0;
        if (abs(disc) < eps) return [label(formatRoot(-a1 / (2 * a2)))];
        if (disc > 0) {
            double sq = sqrt(disc);
            return [label(formatRoot((-a1 + sq) / (2 * a2))),
                    label(formatRoot((-a1 - sq) / (2 * a2)))];
        }
        double re = -a1 / (2 * a2);
        double im = sqrt(-disc) / (2 * a2);
        return [label(formatComplex(re, im)), label(formatComplex(re, -im))];
    }

    // Cubic: normalise, then depress to t^3 + p*t + q via x = t - b/3.
    double b = a2 / a3, c = a1 / a3, d = a0 / a3;
    double p = c - b * b / 3.0;
    double q = 2.0 * b * b * b / 27.0 - b * c / 3.0 + d;
    double shift = b / 3.0;
    double delta = q * q / 4.0 + p * p * p / 27.0;

    if (abs(delta) < 1e-12) {
        if (abs(p) < eps) return [label(formatRoot(-shift))]; // triple root
        double t1 = 3.0 * q / p;
        double t2 = -3.0 * q / (2.0 * p);
        return [label(formatRoot(t1 - shift)), label(formatRoot(t2 - shift))];
    }

    if (delta > 0) {
        // One real root; the other two are a complex conjugate pair.
        double sq = sqrt(delta);
        double u = cbrt(-q / 2.0 + sq);
        double w = cbrt(-q / 2.0 - sq);
        double re = -(u + w) / 2.0 - shift;
        double im = (u - w) * sqrt(3.0) / 2.0;
        return [label(formatRoot(u + w - shift)),
                label(formatComplex(re, im)), label(formatComplex(re, -im))];
    }

    // delta < 0: three distinct real roots (casus irreducibilis).
    double m = 2.0 * sqrt(-p / 3.0);
    double theta = acos(3.0 * q / (2.0 * p) * sqrt(-3.0 / p)) / 3.0;
    string[] roots;
    foreach (k; 0 .. 3)
        roots ~= label(formatRoot(m * cos(theta - 2.0 * PI * k / 3.0) - shift));
    return roots;
}

// 10. Arbitrary-precision equation solving.
//
// The double solver above is capped at ~17 significant digits by its own
// arithmetic. These routines instead work in exact bid/BigInt arithmetic
// and return roots to as many decimal places as asked for.

BigInt isqrt(BigInt n) {
    enforce(n >= 0, "isqrt of a negative value");
    if (n < 2) return n;
    // Start above the true root so the Newton iteration descends onto it.
    BigInt x = pow10(cast(int)((n.toDecimalString().length + 2) / 2));
    BigInt y = (x + n / x) / 2;
    while (y < x) { x = y; y = (x + n / x) / 2; }
    return x;
}

BigInt icbrt(BigInt n) {
    bool neg = n < 0;
    if (neg) n = -n;
    if (n < 2) return neg ? -n : n;
    BigInt x = pow10(cast(int)((n.toDecimalString().length + 3) / 3));
    BigInt y = (2 * x + n / (x * x)) / 3;
    while (y < x) { x = y; y = (2 * x + n / (x * x)) / 3; }
    return neg ? -x : x;
}

// Builds a bid from a signed BigInt, restoring the sign/magnitude split
// the struct expects.
private bid bidSigned(BigInt v, int exp) {
    bool neg = v < 0;
    return bid(neg, neg ? -v : v, exp);
}

// Rounds to `scale` decimal places, round-half-up. Keeps intermediate
// values from growing without bound during iteration.
bid bidRound(bid v, int scale) {
    if (-v.exponent <= scale) return v;
    int drop = -v.exponent - scale;
    BigInt d = pow10(drop);
    BigInt q = v.coefficient / d;
    if ((v.coefficient % d) * 2 >= d) q += 1;
    return bid(v.negative && q != 0, q, -scale);
}

// Square root to `scale` decimal places, via integer sqrt of the value
// shifted left by 2*scale digits. Truncates rather than rounds, so the
// result never overstates the root; pair with bidRound if the
// nearest-value answer is what you want.
bid bidSqrt(bid v, int scale) {
    enforce(!v.negative, "bidSqrt of a negative value");
    int shift = v.exponent + 2 * scale;
    BigInt n = v.coefficient;
    if (shift >= 0) n *= pow10(shift);
    else n /= pow10(-shift);
    return bid(false, isqrt(n), -scale);
}

// Cube root to `scale` decimal places; handles negative input.
bid bidCbrt(bid v, int scale) {
    int shift = v.exponent + 3 * scale;
    BigInt n = v.coefficient;
    if (shift >= 0) n *= pow10(shift);
    else n /= pow10(-shift);
    return bid(v.negative, icbrt(n), -scale);
}

// Horner evaluation, rounding after each step so the working precision
// stays bounded instead of tripling with every multiply.
private bid polyEval(bid[] coeffs, bid x, int scale) {
    bid acc = bid(0L);
    foreach_reverse (c; coeffs)
        acc = bidRound(acc * x + c, scale);
    return acc;
}

private bid[] polyDeriv(bid[] coeffs) {
    bid[] d;
    foreach (i; 1 .. coeffs.length)
        d ~= coeffs[i] * bid(cast(long)i);
    return d;
}

// Newton refinement of a root, in exact arithmetic. `multiplicity` > 1
// restores quadratic convergence on repeated roots, where plain Newton
// would crawl.
bid refineRoot(bid[] coeffs, bid guess, int multiplicity, int scale) {
    bid[] deriv = polyDeriv(coeffs);
    bid x = bidRound(guess, scale);
    foreach (_; 0 .. 500) {
        bid fx = polyEval(coeffs, x, scale);
        bid dfx = polyEval(deriv, x, scale);
        if (dfx.coefficient == 0) break;
        bid step = fx.divide(dfx, scale);
        if (multiplicity > 1) step = step * bid(cast(long)multiplicity);
        bid next = bidRound(x - step, scale);
        if ((next - x).coefficient == 0) return next;
        x = next;
    }
    return x;
}

private string labelRoot(char v, bid value) {
    return v ~ ": " ~ value.toString();
}

private string labelComplex(char v, bid re, bid im) {
    bool negIm = im.negative;
    bid mag = bid(false, im.coefficient, im.exponent);
    return v ~ ": " ~ re.toString() ~ (negIm ? " - " : " + ") ~ mag.toString() ~ "i";
}

// Solves a degree 1-3 equation to `scale` decimal places using exact
// decimal arithmetic throughout. Same equation syntax as solve().
//
// Degree 1, degree 2, and the repeated-root cubics are closed-form and
// exact. The remaining cubics are seeded from the double solver and then
// Newton-refined in exact arithmetic, which is what carries them past
// double's ~17 digits.
string[] solvePrecise(string varName, string equation, int scale) {
    enforce(scale >= 0, "scale must not be negative");
    char v = varName.length ? varName[0] : 'x';
    int work = scale + 20; // guard digits, trimmed on the way out

    bid[4] c = equationCoeffs(equation, v);
    bid a3 = c[3], a2 = c[2], a1 = c[1], a0 = c[0];

    bool isZero(bid b) { return b.coefficient == 0; }
    string outRoot(bid r) { return labelRoot(v, bidRound(r, scale)); }

    if (isZero(a3) && isZero(a2) && isZero(a1))
        return isZero(a0) ? ["infinitely many solutions"] : ["no solution"];

    // Linear: exact.
    if (isZero(a3) && isZero(a2)) {
        bid root = a0.divide(a1, work);
        root.negative = !root.negative && !isZero(root);
        return [outRoot(root)];
    }

    // Quadratic: exact, with an arbitrary-precision square root.
    if (isZero(a3)) {
        bid disc = a1 * a1 - bid(4L) * a2 * a0;
        bid twoA = bid(2L) * a2;
        bid negB = a1;
        negB.negative = !negB.negative && !isZero(negB);

        if (isZero(disc)) return [outRoot(negB.divide(twoA, work))];

        if (!disc.negative) {
            bid sq = bidSqrt(disc, work);
            return [outRoot((negB + sq).divide(twoA, work)),
                    outRoot((negB - sq).divide(twoA, work))];
        }
        bid re = negB.divide(twoA, work);
        bid im = bidSqrt(bid(false, disc.coefficient, disc.exponent), work)
                    .divide(twoA, work);
        return [labelComplex(v, bidRound(re, scale), bidRound(im, scale)),
                labelComplex(v, bidRound(re, scale),
                             bidRound(bidSigned(-im.coefficient, im.exponent), scale))];
    }

    // Cubic. Classify exactly, then solve each case at full precision.
    bid disc = bid(18L) * a3 * a2 * a1 * a0
             - bid(4L) * a2 * a2 * a2 * a0
             + a2 * a2 * a1 * a1
             - bid(4L) * a3 * a1 * a1 * a1
             - bid(27L) * a3 * a3 * a0 * a0;
    bid b2m3ac = a2 * a2 - bid(3L) * a3 * a1;

    if (isZero(disc)) {
        // Triple root: x = -a2 / (3*a3), exact.
        if (isZero(b2m3ac)) {
            bid root = a2.divide(bid(3L) * a3, work);
            root.negative = !root.negative && !isZero(root);
            return [outRoot(root)];
        }
        // Double root plus a simple root; both are exact rationals.
        bid dbl = (bid(9L) * a3 * a0 - a2 * a1).divide(bid(2L) * b2m3ac, work);
        bid simple = (bid(4L) * a3 * a2 * a1 - bid(9L) * a3 * a3 * a0 - a2 * a2 * a2)
                        .divide(a3 * b2m3ac, work);
        return [outRoot(dbl), outRoot(simple)];
    }

    // Seed every real root from the double solver, then refine exactly.
    bid[] poly = [a0, a1, a2, a3];
    double da3 = getDouble(a3), da2 = getDouble(a2),
           da1 = getDouble(a1), da0 = getDouble(a0);
    double b = da2 / da3, cc = da1 / da3, d = da0 / da3;
    double p = cc - b * b / 3.0;
    double q = 2.0 * b * b * b / 27.0 - b * cc / 3.0 + d;
    double shift = b / 3.0;

    if (disc.negative) {
        // One real root, one complex conjugate pair.
        double sq = sqrt(q * q / 4.0 + p * p * p / 27.0);
        double seed = cbrt(-q / 2.0 + sq) + cbrt(-q / 2.0 - sq) - shift;
        bid root = refineRoot(poly, bid(seed), 1, work);

        // Deflate by (x - root) and solve the remaining quadratic exactly.
        bid q2 = a3;
        bid q1 = a2 + a3 * root;
        bid q0 = a1 + root * q1;
        bid dsc = q1 * q1 - bid(4L) * q2 * q0;
        bid twoA = bid(2L) * q2;
        bid negB = q1;
        negB.negative = !negB.negative && !isZero(negB);
        bid re = negB.divide(twoA, work);
        bid im = bidSqrt(bid(false, dsc.coefficient, dsc.exponent), work)
                    .divide(twoA, work);
        return [outRoot(root),
                labelComplex(v, bidRound(re, scale), bidRound(im, scale)),
                labelComplex(v, bidRound(re, scale),
                             bidRound(bidSigned(-im.coefficient, im.exponent), scale))];
    }

    // Three distinct real roots (casus irreducibilis).
    double m = 2.0 * sqrt(-p / 3.0);
    double theta = acos(3.0 * q / (2.0 * p) * sqrt(-3.0 / p)) / 3.0;
    string[] roots;
    foreach (k; 0 .. 3) {
        double seed = m * cos(theta - 2.0 * PI * k / 3.0) - shift;
        roots ~= outRoot(refineRoot(poly, bid(seed), 1, work));
    }
    return roots;
}

// Same as solvePrecise, but hands back the real roots as dpd values so
// they can be packed into declets or fed into further decimal work.
dpd[] solveRealRoots(string varName, string equation, int scale) {
    dpd[] roots;
    foreach (entry; solvePrecise(varName, equation, scale)) {
        auto colon = entry.indexOf(": ");
        if (colon == -1) continue;              // "no solution" and friends
        string value = entry[colon + 2 .. $];
        if (value.indexOf('i') != -1) continue; // skip the complex pairs
        roots ~= dpd(value);
    }
    return roots;
}

unittest {
    assert(gcd(48, 18) == 6);
    assert(lcm(4, 6) == 12);

    dfloat a = dfloat(2.0);
    fra b = fra(1, 2);

    // dfloat + fra -> fra
    auto res1 = a + b;
    assert(is(typeof(res1) == fra));
    assert(res1.num == 5 && res1.den == 2);
}

// 7. Densely Packed Decimal (IEEE 754-2008) bit-level codec.
// Boolean equations per the reference DPD encoding, as published by
// Mike Cowlishaw (https://speleotrove.com/decimal/DPDecimal.html).
// digit2 (left) = bits a,b,c,d; digit1 (middle) = e,f,g,h; digit0 (right) = i,j,k,m.
ushort bcdToDpd(ubyte d2, ubyte d1, ubyte d0) {
    bool a = (d2 & 8) != 0, b = (d2 & 4) != 0, c = (d2 & 2) != 0, d = (d2 & 1) != 0;
    bool e = (d1 & 8) != 0, f = (d1 & 4) != 0, g = (d1 & 2) != 0, h = (d1 & 1) != 0;
    bool i = (d0 & 8) != 0, j = (d0 & 4) != 0, k = (d0 & 2) != 0, m = (d0 & 1) != 0;

    bool p = b || (a && j) || (a && f && i);
    bool q = c || (a && k) || (a && g && i);
    bool r = d;
    bool s = (f && (!a || !i)) || (!a && e && j) || (e && i);
    bool t = g || (!a && e && k) || (a && i);
    bool u = h;
    bool v = a || e || i;
    bool w = a || (e && i) || (!e && j);
    bool x = e || (a && i) || (!a && k);
    bool y = m;

    ushort result = 0;
    foreach (bit_; [p, q, r, s, t, u, v, w, x, y])
        result = cast(ushort)((result << 1) | (bit_ ? 1 : 0));
    return result;
}

void dpdToBcd(ushort declet, out ubyte d2, out ubyte d1, out ubyte d0) {
    bool bitAt(int pos) { return ((declet >> (9 - pos)) & 1) != 0; }
    bool p = bitAt(0), q = bitAt(1), r = bitAt(2), s = bitAt(3), t = bitAt(4);
    bool u = bitAt(5), v = bitAt(6), w = bitAt(7), x = bitAt(8), y = bitAt(9);

    bool a = (v && w) && (!s || t || !x);
    bool b = p && (!v || !w || (s && !t && x));
    bool c = q && (!v || !w || (s && !t && x));
    bool d = r;
    bool e = v && ((!w && x) || (!t && x) || (s && x));
    bool f = (s && (!v || !x)) || (p && !s && t && v && w && x);
    bool g = (t && (!v || !x)) || (q && !s && t && w);
    bool h = u;
    bool i = v && ((!w && !x) || (w && x && (s || t)));
    bool j = (!v && w) || (s && v && !w && x) || (p && w && (!x || (!s && !t)));
    bool k = (!v && x) || (t && !w && x) || (q && v && w && (!x || (!s && !t)));
    bool m = y;

    d2 = cast(ubyte)((a ? 8 : 0) | (b ? 4 : 0) | (c ? 2 : 0) | (d ? 1 : 0));
    d1 = cast(ubyte)((e ? 8 : 0) | (f ? 4 : 0) | (g ? 2 : 0) | (h ? 1 : 0));
    d0 = cast(ubyte)((i ? 8 : 0) | (j ? 4 : 0) | (k ? 2 : 0) | (m ? 1 : 0));
}

string zeroPad(size_t n) {
    string r;
    foreach (_; 0 .. n) r ~= '0';
    return r;
}

BigInt pow10(int n) {
    BigInt r = BigInt(1);
    foreach (_; 0 .. n) r *= 10;
    return r;
}

// Shortest fixed-point decimal string that parses back to the exact same
// double bit pattern (mirrors Python's `str(x)` / repr algorithm). This
// recovers what the source literal most likely was (0.1, 1.5, even
// 1.1 + 2.2 -> "3.3"), but it can never exceed a double's own ~17
// significant-digit resolution -- it is not a substitute for a string
// literal when more than that many exact digits are needed.
string doubleToExactString(double v) {
    foreach (prec; 0 .. 21) {
        string s = format("%.*f", prec, v);
        if (to!double(s) == v) return s;
    }
    return format("%.20f", v);
}

// 8. bid (Binary Integer Decimal): coefficient stored as a plain
// arbitrary-precision binary integer. value = sign * coefficient * 10^exponent.
struct bid {
    bool negative;
    BigInt coefficient;
    int exponent;

    this(bool neg, BigInt coeff, int exp) {
        negative = neg;
        coefficient = coeff;
        exponent = exp;
    }

    // Enables direct declaration from an integer literal: bid one = 1;
    this(long v) {
        negative = v < 0;
        coefficient = BigInt(negative ? -v : v);
        exponent = 0;
    }

    // Enables direct declaration from a plain decimal literal: bid x = 1.5;
    // See doubleToExactString for what this can and cannot recover exactly.
    this(double v) {
        this(doubleToExactString(v));
    }

    this(string s) {
        string str = s;
        negative = false;
        if (str.length && (str[0] == '-' || str[0] == '+')) {
            negative = (str[0] == '-');
            str = str[1 .. $];
        }
        auto dot = str.indexOf('.');
        string intPart = dot == -1 ? str : str[0 .. dot];
        string fracPart = dot == -1 ? "" : str[dot + 1 .. $];
        exponent = -cast(int)fracPart.length;
        string digitsStr = intPart ~ fracPart;
        coefficient = digitsStr.length ? BigInt(digitsStr) : BigInt(0);
        if (coefficient == 0) negative = false;
    }

    private static void alignCoeffs(BigInt c1, int e1, BigInt c2, int e2,
                                     out BigInt a1, out BigInt a2, out int commonExp) {
        if (e1 == e2) {
            a1 = c1; a2 = c2; commonExp = e1;
        } else if (e1 > e2) {
            a1 = c1 * pow10(e1 - e2); a2 = c2; commonExp = e2;
        } else {
            a1 = c1; a2 = c2 * pow10(e2 - e1); commonExp = e1;
        }
    }

    bid opBinary(string op)(bid rhs) const if (op == "+" || op == "-") {
        BigInt ca, cb; int ce;
        alignCoeffs(coefficient, exponent, rhs.coefficient, rhs.exponent, ca, cb, ce);
        BigInt sa = negative ? -ca : ca;
        BigInt sb = rhs.negative ? -cb : cb;
        BigInt sum = (op == "+") ? sa + sb : sa - sb;
        bool neg = sum < 0;
        BigInt mag = neg ? -sum : sum;
        return bid(neg, mag, ce);
    }

    bid opBinary(string op)(bid rhs) const if (op == "*") {
        return bid(negative != rhs.negative, coefficient * rhs.coefficient, exponent + rhs.exponent);
    }

    // Lets bid mix with plain numbers/strings on the right: x + 1, x - "0.5", x * 3
    bid opBinary(string op, T)(T rhs) const
            if (!is(Unqual!T == bid) && __traits(compiles, bid(rhs))) {
        return this.opBinary!op(bid(rhs));
    }

    // ...and on the left: 1 + x, 10 - x
    bid opBinaryRight(string op, T)(T lhs) const
            if (!is(Unqual!T == bid) && __traits(compiles, bid(lhs))) {
        return bid(lhs).opBinary!op(this);
    }

    int opCmp(bid rhs) const {
        BigInt ca, cb; int ce;
        alignCoeffs(coefficient, exponent, rhs.coefficient, rhs.exponent, ca, cb, ce);
        BigInt a = negative ? -ca : ca;
        BigInt b = rhs.negative ? -cb : cb;
        if (a < b) return -1;
        if (a > b) return 1;
        return 0;
    }

    bool opEquals(bid rhs) const { return opCmp(rhs) == 0; }

    int opCmp(T)(T rhs) const if (!is(Unqual!T == bid) && __traits(compiles, bid(rhs))) {
        return opCmp(bid(rhs));
    }

    bool opEquals(T)(T rhs) const if (!is(Unqual!T == bid) && __traits(compiles, bid(rhs))) {
        return opEquals(bid(rhs));
    }

    // Divides with a fixed number of fractional decimal digits, round-half-up.
    bid divide(bid rhs, int scale) const {
        int shift = exponent - rhs.exponent + scale;
        BigInt num = coefficient;
        BigInt den = rhs.coefficient;
        if (shift >= 0) num *= pow10(shift);
        else den *= pow10(-shift);
        BigInt q = num / den;
        BigInt r = num % den;
        if (r * 2 >= den) q += 1;
        return bid(negative != rhs.negative, q, -scale);
    }

    bid divide(T)(T rhs, int scale) const
            if (!is(Unqual!T == bid) && __traits(compiles, bid(rhs))) {
        return divide(bid(rhs), scale);
    }

    // Arbitrary-precision roots and rounding, callable directly on a value.
    bid sqrt(int scale) const { return bidSqrt(this, scale); }
    bid cbrt(int scale) const { return bidCbrt(this, scale); }
    bid round(int scale) const { return bidRound(this, scale); }

    string toString() const {
        string sign = negative ? "-" : "";
        string s = coefficient.toDecimalString();
        if (exponent >= 0) return sign ~ s ~ zeroPad(exponent);
        int fracLen = -exponent;
        if (s.length <= fracLen) s = zeroPad(fracLen - s.length + 1) ~ s;
        return sign ~ s[0 .. $ - fracLen] ~ "." ~ s[$ - fracLen .. $];
    }
}

// 9. dpd (Densely Packed Decimal): same abstract decimal value as bid,
// but digits are grouped in 3s and each group packed into a 10-bit
// declet via bcdToDpd/dpdToBcd, mirroring IEEE 754-2008 decimalNN storage.
struct dpd {
    bool negative;
    ubyte[] digits; // most-significant digit first, each 0-9
    int exponent;

    this(bool neg, ubyte[] digs, int exp) {
        negative = neg;
        digits = digs.length ? digs : [cast(ubyte)0];
        exponent = exp;
    }

    // Enables direct declaration from an integer literal: dpd one = 1;
    this(long v) {
        bid tmp = bid(v);
        this(tmp.negative, digitsFromBigInt(tmp.coefficient), 0);
    }

    // Enables direct declaration from a plain decimal literal: dpd x = 1.5;
    // See doubleToExactString for what this can and cannot recover exactly.
    this(double v) {
        this(doubleToExactString(v));
    }

    this(string s) {
        bid tmp = bid(s);
        this(tmp.negative, digitsFromBigInt(tmp.coefficient), tmp.exponent);
    }

    static ubyte[] digitsFromBigInt(BigInt v) {
        if (v == 0) return [0];
        ubyte[] rev;
        BigInt ten = BigInt(10);
        while (v > 0) {
            rev ~= cast(ubyte)((v % ten).toLong());
            v /= ten;
        }
        ubyte[] result = new ubyte[rev.length];
        foreach (idx, dgt; rev) result[$ - 1 - idx] = dgt;
        return result;
    }

    BigInt toBigInt() const {
        BigInt result = BigInt(0);
        foreach (dgt; digits) result = result * 10 + dgt;
        return result;
    }

    bid toBid() const { return bid(negative, toBigInt(), exponent); }

    static dpd fromBid(bid b) {
        return dpd(b.negative, digitsFromBigInt(b.coefficient), b.exponent);
    }

    dpd opBinary(string op)(dpd rhs) const if (op == "+" || op == "-" || op == "*") {
        return dpd.fromBid(mixin("toBid() " ~ op ~ " rhs.toBid()"));
    }

    // Lets dpd mix with plain numbers/strings on either side, same as bid.
    dpd opBinary(string op, T)(T rhs) const
            if (!is(Unqual!T == dpd) && __traits(compiles, dpd(rhs))) {
        return this.opBinary!op(dpd(rhs));
    }

    dpd opBinaryRight(string op, T)(T lhs) const
            if (!is(Unqual!T == dpd) && __traits(compiles, dpd(lhs))) {
        return dpd(lhs).opBinary!op(this);
    }

    int opCmp(dpd rhs) const { return toBid().opCmp(rhs.toBid()); }
    bool opEquals(dpd rhs) const { return toBid().opEquals(rhs.toBid()); }

    int opCmp(T)(T rhs) const if (!is(Unqual!T == dpd) && __traits(compiles, dpd(rhs))) {
        return opCmp(dpd(rhs));
    }

    bool opEquals(T)(T rhs) const if (!is(Unqual!T == dpd) && __traits(compiles, dpd(rhs))) {
        return opEquals(dpd(rhs));
    }

    dpd divide(dpd rhs, int scale) const {
        return dpd.fromBid(toBid().divide(rhs.toBid(), scale));
    }

    dpd divide(T)(T rhs, int scale) const
            if (!is(Unqual!T == dpd) && __traits(compiles, dpd(rhs))) {
        return divide(dpd(rhs), scale);
    }

    // Arbitrary-precision roots and rounding, without hopping through bid.
    dpd sqrt(int scale) const { return dpd.fromBid(bidSqrt(toBid(), scale)); }
    dpd cbrt(int scale) const { return dpd.fromBid(bidCbrt(toBid(), scale)); }
    dpd round(int scale) const { return dpd.fromBid(bidRound(toBid(), scale)); }

    // Packs digits into 10-bit declets, left-padding with zero digits
    // so the digit count is a multiple of 3.
    ushort[] pack() const {
        size_t pad = (3 - digits.length % 3) % 3;
        ubyte[] padded = new ubyte[pad] ~ digits;
        ushort[] result;
        for (size_t idx = 0; idx < padded.length; idx += 3)
            result ~= bcdToDpd(padded[idx], padded[idx + 1], padded[idx + 2]);
        return result;
    }

    static ubyte[] unpackDigits(ushort[] declets) {
        ubyte[] result;
        foreach (declet; declets) {
            ubyte d2, d1, d0;
            dpdToBcd(declet, d2, d1, d0);
            result ~= d2; result ~= d1; result ~= d0;
        }
        return result;
    }

    string toString() const { return toBid().toString(); }
}

unittest {
    // Exhaustive round-trip over every 3-digit decimal value (000-999).
    foreach (ubyte a; 0 .. 10) foreach (ubyte b; 0 .. 10) foreach (ubyte c; 0 .. 10) {
        ushort code = bcdToDpd(a, b, c);
        ubyte ra, rb, rc;
        dpdToBcd(code, ra, rb, rc);
        assert(ra == a && rb == b && rc == c);
    }

    bid one = 1;
    bid three = 3;
    assert(one.divide(three, 3).toString() == "0.333");

    bid x = bid("1.5");
    bid y = bid("2.25");
    assert((x + y).toString() == "3.75");
    assert((x * y).toString() == "3.375");

    dpd dx = dpd("1.5");
    dpd dy = dpd("2.25");
    assert((dx + dy).toString() == "3.75");
    ubyte[] roundTripped = dpd.unpackDigits(dx.pack());
    assert(dpd(false, roundTripped, 0).toBigInt() == dx.toBigInt());

    // Mixing a string-declared bid/dpd with plain numbers and strings.
    bid mx = "1.5";
    assert((mx + 1).toString() == "2.5");
    assert((1 + mx).toString() == "2.5");
    assert((mx - "0.5").toString() == "1.0");
    assert(mx > 1);
    assert(mx == "1.50");

    dpd my = "1.5";
    assert((my + 1).toString() == "2.5");
    assert(my == "1.5");

    // fra must interoperate exactly with bid/dpd, not silently treat them as 0.
    fra half = fra(1, 2);
    bid oneQuarter = "0.25";
    dpd oneQuarterD = "0.25";
    assert((half + oneQuarter) == fra(3, 4));
    assert((half + oneQuarterD) == fra(3, 4));

    fra fromSlash = "3/4";
    fra fromDecimal = "0.75";
    assert(fromSlash.num == fromDecimal.num && fromSlash.den == fromDecimal.den);

    fra five = 5;
    assert(five.num == 5 && five.den == 1);

    // Plain decimal literals (no quotes) work via shortest round-trip.
    bid literalA = 1.5;
    assert(literalA.toString() == "1.5");
    bid literalB = 0.1;
    assert(literalB.toString() == "0.1");
    bid literalC = 1.1 + 2.2;
    assert(literalC.toString() == "3.3");

    dpd literalD = 2.25;
    assert(literalD.toString() == "2.25");

    // solve: degree 1
    assert(solve("x", "x + 5 = 12") == ["x: 7"]);
    assert(solve("x", "2*x = 10") == ["x: 5"]);
    assert(solve("x", "3x - 9 = 0") == ["x: 3"]);

    // solve: degree 2, including terms on both sides and a repeated root
    assert(solve("x", "x^2 - 5x + 6 = 0") == ["x: 3", "x: 2"]);
    assert(solve("x", "x^2 = 2x + 3") == ["x: 3", "x: -1"]);
    assert(solve("x", "x^2 - 2x + 1 = 0") == ["x: 1"]);
    assert(solve("x", "x^2 + 1 = 0") == ["x: 0 + 1i", "x: 0 - 1i"]);

    // solve: degree 3 -- distinct real, triple, and one real + conjugate pair
    assert(solve("x", "x^3 - 6x^2 + 11x - 6 = 0") == ["x: 3", "x: 2", "x: 1"]);
    assert(solve("x", "x^3 - 3x^2 + 3x - 1 = 0") == ["x: 1"]);
    assert(solve("x", "x^3 = 8")
           == ["x: 2", "x: -1 + 1.732050808i", "x: -1 - 1.732050808i"]);

    // solve: a variable other than x, and the degenerate cases
    assert(solve("y", "2y - 8 = 0") == ["y: 4"]);
    assert(solve("x", "x - x = 0") == ["infinitely many solutions"]);
    assert(solve("x", "x - x = 5") == ["no solution"]);

    // solve: degree above 3 is rejected rather than silently mis-solved
    bool threw = false;
    try { solve("x", "x^4 = 1"); } catch (Exception) { threw = true; }
    assert(threw);

    // Arbitrary-precision roots, checked against the known expansions.
    // sqrt(2)  = 1.4142135623730950488016887242096980785696718753769480...
    // cbrt(2)  = 1.2599210498948731647672106072782283505702514647015079...
    enum sqrt2_50 = "1.41421356237309504880168872420969807856967187537695";
    enum cbrt2_50 = "1.25992104989487316476721060727822835057025146470151";
    assert(solvePrecise("x", "x^2 - 2 = 0", 50) == ["x: " ~ sqrt2_50, "x: -" ~ sqrt2_50]);
    assert(solvePrecise("x", "x^3 - 2 = 0", 50)[0] == "x: " ~ cbrt2_50);

    // The closed-form path and the integer-root path must agree.
    assert(bidRound(bidSqrt(bid(2L), 60), 50).toString() == sqrt2_50);
    assert(bidRound(bidCbrt(bid(2L), 60), 50).toString() == cbrt2_50);

    // A root fed back through exact multiplication reproduces the input.
    bid r2 = bidSqrt(bid(2L), 60);
    assert(bidRound(r2 * r2, 55) == bid(2L));

    // Exact rational cases stay exact at any scale.
    assert(solvePrecise("x", "2x - 1 = 0", 25) == ["x: 0.5000000000000000000000000"]);
    assert(solvePrecise("x", "x^2 - 5x + 6 = 0", 4) == ["x: 3.0000", "x: 2.0000"]);
    assert(solvePrecise("x", "x^3 - 3x^2 + 3x - 1 = 0", 4) == ["x: 1.0000"]);

    // Casus irreducibilis: 2cos(2pi/9), 2cos(4pi/9), 2cos(8pi/9).
    assert(solvePrecise("x", "x^3 - 3x + 1 = 0", 20)
           == ["x: 1.53208888623795607040", "x: 0.34729635533386069770",
               "x: -1.87938524157181676811"]);

    // Real roots come back as dpd values that pack into declets.
    auto dpdRoots = solveRealRoots("x", "x^2 - 2 = 0", 45);
    assert(dpdRoots.length == 2);
    assert(dpdRoots[0].digits.length == 46);
    assert(dpdRoots[0].pack().length == 16);
    assert(dpd.unpackDigits(dpdRoots[0].pack())[$ - 46 .. $] == dpdRoots[0].digits);

    assert(solvePrecise("x", "x^2 + 1 = 0", 3)
           == ["x: 0.000 + 1.000i", "x: 0.000 - 1.000i"]);
    assert(solveRealRoots("x", "x^2 + 1 = 0", 3).length == 0);

    // sqrt/cbrt/round are callable straight off a value, on both types.
    dpd dTwo = 2;
    bid bTwo = 2;
    assert(dTwo.sqrt(40).toString() == bTwo.sqrt(40).toString());
    assert(dTwo.cbrt(40).toString() == bTwo.cbrt(40).toString());
    assert(dTwo.sqrt(40).round(10).toString() == "1.4142135624");

    // The roots truncate; rounding is opt-in via an extra digit and round().
    assert(dTwo.sqrt(40).toString().length == 42);       // "1." + 40 digits
    assert(dTwo.sqrt(40).toString()[$ - 1] == '6');      // truncated
    assert(dTwo.sqrt(45).round(40).toString()[$ - 1] == '7'); // rounded
}
