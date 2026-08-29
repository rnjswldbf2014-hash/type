module type.type;

import std.stdio;
import std.conv;
import std.string;
import std.math;
import std.algorithm;
import std.exception;
import std.traits;

// Helper to extract double value
double getDouble(T)(T v) {
    alias UT = Unqual!T;
    static if (isNumeric!UT) return to!double(v);
    else static if (is(UT == fra)) return to!double(v.num) / to!double(v.den);
    else static if (is(UT == dfloat)) return v.val;
    else static if (is(UT == dec)) return v.val;
    else static if (is(UT == posit)) return v.val;
    else return 0.0;
}

// Helper to convert to fraction
fra getFra(T)(T v) {
    alias UT = Unqual!T;
    static if (is(UT == fra)) {
        return v;
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

// 2. fra (Fraction)
struct fra {
    long num;
    long den;
    
    this(long numerator, long denominator) {
        enforce(denominator != 0, "Denominator cannot be zero");
        num = numerator;
        den = denominator;
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
