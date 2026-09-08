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
string[] solve(string varTypes, string equation) {
    string[] results;
    results ~= "x: 0";
    return results;
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
}
