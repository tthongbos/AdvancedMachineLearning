#include <bits/stdc++.h>
using namespace std;

/*
    ============================================================
    FULL DEMO:
    - Built-in multiplication in C++: int / long long / unsigned long long / double
    - BigInt exact multiplication: schoolbook O(n^2)
    - Karatsuba exact multiplication: O(n^log2(3)) ~= O(n^1.585)
    - Benchmark and many examples
    ============================================================

    Compile:
        g++ -std=c++17 -O2 -Wall -Wextra -pedantic full_demo.cpp -o full_demo

    Run:
        ./full_demo
*/

// ============================================================
// BigInt (non-negative only), stored in base 10, little-endian
// Example: 1234 => [4,3,2,1]
// ============================================================

using BigInt = vector<int>;

static inline void trim(BigInt &a) {
    while (a.size() > 1 && a.back() == 0) a.pop_back();
}

static inline BigInt fromString(const string &s) {
    if (s.empty()) throw runtime_error("Empty string is not a valid integer");

    BigInt a;
    a.reserve(s.size());

    int start = 0;
    if (s[0] == '+') start = 1;
    if (start >= (int)s.size()) throw runtime_error("Invalid integer string");

    for (int i = (int)s.size() - 1; i >= start; --i) {
        if (!isdigit((unsigned char)s[i])) {
            throw runtime_error("Invalid digit in integer string: " + s);
        }
        a.push_back(s[i] - '0');
    }

    trim(a);
    return a;
}

static inline string toString(const BigInt &a) {
    if (a.empty()) return "0";
    string s;
    s.reserve(a.size());
    for (int i = (int)a.size() - 1; i >= 0; --i) {
        s.push_back(char('0' + a[i]));
    }
    return s.empty() ? "0" : s;
}

static inline int compareBigInt(const BigInt &a, const BigInt &b) {
    if (a.size() != b.size()) return (a.size() < b.size() ? -1 : 1);
    for (int i = (int)a.size() - 1; i >= 0; --i) {
        if (a[i] != b[i]) return (a[i] < b[i] ? -1 : 1);
    }
    return 0;
}

static inline BigInt addBigInt(const BigInt &a, const BigInt &b) {
    BigInt res;
    int n = max(a.size(), b.size());
    res.reserve(n + 1);

    int carry = 0;
    for (int i = 0; i < n || carry; ++i) {
        int cur = carry;
        if (i < (int)a.size()) cur += a[i];
        if (i < (int)b.size()) cur += b[i];
        res.push_back(cur % 10);
        carry = cur / 10;
    }

    trim(res);
    return res;
}

static inline BigInt subBigInt(const BigInt &a, const BigInt &b) {
    // Assume a >= b, both non-negative
    if (compareBigInt(a, b) < 0) {
        throw runtime_error("subBigInt requires a >= b");
    }

    BigInt res = a;
    int borrow = 0;

    for (int i = 0; i < (int)res.size(); ++i) {
        int cur = res[i] - borrow - (i < (int)b.size() ? b[i] : 0);
        if (cur < 0) {
            cur += 10;
            borrow = 1;
        } else {
            borrow = 0;
        }
        res[i] = cur;
    }

    trim(res);
    return res;
}

static inline BigInt shiftLeftDigits(const BigInt &a, int k) {
    // multiply by 10^k
    if ((a.size() == 1 && a[0] == 0) || k == 0) return a;
    BigInt res(k, 0);
    res.insert(res.end(), a.begin(), a.end());
    return res;
}

static BigInt schoolbookMultiply(const BigInt &a, const BigInt &b) {
    if ((a.size() == 1 && a[0] == 0) || (b.size() == 1 && b[0] == 0)) return {0};

    BigInt res(a.size() + b.size(), 0);

    for (int i = 0; i < (int)a.size(); ++i) {
        int carry = 0;
        for (int j = 0; j < (int)b.size() || carry; ++j) {
            long long cur = res[i + j]
                          + 1LL * a[i] * (j < (int)b.size() ? b[j] : 0)
                          + carry;
            res[i + j] = int(cur % 10);
            carry = int(cur / 10);
        }
    }

    trim(res);
    return res;
}

static BigInt karatsuba(const BigInt &x, const BigInt &y) {
    if ((x.size() == 1 && x[0] == 0) || (y.size() == 1 && y[0] == 0)) return {0};

    int n = max(x.size(), y.size());

    // For small sizes, schoolbook is usually faster because of smaller constant factor
    if (n <= 32) return schoolbookMultiply(x, y);

    int m = n / 2;

    BigInt a0(x.begin(), x.begin() + min<int>(x.size(), m));
    BigInt a1(x.begin() + min<int>(x.size(), m), x.end());

    BigInt b0(y.begin(), y.begin() + min<int>(y.size(), m));
    BigInt b1(y.begin() + min<int>(y.size(), m), y.end());

    if (a0.empty()) a0 = {0};
    if (a1.empty()) a1 = {0};
    if (b0.empty()) b0 = {0};
    if (b1.empty()) b1 = {0};

    trim(a0); trim(a1); trim(b0); trim(b1);

    BigInt z0 = karatsuba(a0, b0);
    BigInt z2 = karatsuba(a1, b1);

    BigInt sumA = addBigInt(a0, a1);
    BigInt sumB = addBigInt(b0, b1);
    BigInt z1 = karatsuba(sumA, sumB);

    // z1 = (a0+a1)(b0+b1) - z0 - z2
    z1 = subBigInt(subBigInt(z1, z0), z2);

    BigInt res = addBigInt(
        addBigInt(shiftLeftDigits(z2, 2 * m), shiftLeftDigits(z1, m)),
        z0
    );

    trim(res);
    return res;
}

// ============================================================
// Helpers for built-in integer fit / overflow checking
// ============================================================

static inline bool isDigitsOnly(const string &s) {
    if (s.empty()) return false;
    int start = (s[0] == '+' ? 1 : 0);
    if (start == (int)s.size()) return false;
    for (int i = start; i < (int)s.size(); ++i) {
        if (!isdigit((unsigned char)s[i])) return false;
    }
    return true;
}

static inline string stripLeadingZeros(string s) {
    int start = 0;
    if (!s.empty() && s[0] == '+') start = 1;

    int i = start;
    while (i < (int)s.size() && s[i] == '0') ++i;

    string core = (i == (int)s.size() ? "0" : s.substr(i));
    return core;
}

static bool fitsUnsignedLongLongString(const string &s) {
    if (!isDigitsOnly(s)) return false;
    string x = stripLeadingZeros(s);
    const string LIMIT = "18446744073709551615"; // ULLONG_MAX
    if (x.size() != LIMIT.size()) return x.size() < LIMIT.size();
    return x <= LIMIT;
}

static bool fitsLongLongStringNonNegative(const string &s) {
    if (!isDigitsOnly(s)) return false;
    string x = stripLeadingZeros(s);
    const string LIMIT = "9223372036854775807"; // LLONG_MAX
    if (x.size() != LIMIT.size()) return x.size() < LIMIT.size();
    return x <= LIMIT;
}

static unsigned long long parseULLChecked(const string &s) {
    // Precondition: fitsUnsignedLongLongString(s) == true
    return stoull(s);
}

static long long parseLLChecked(const string &s) {
    // Precondition: fitsLongLongStringNonNegative(s) == true
    return stoll(s);
}

static bool willOverflowULLMul(unsigned long long a, unsigned long long b) {
    if (a == 0 || b == 0) return false;
    return a > ULLONG_MAX / b;
}

static bool willOverflowLLMulNonNegative(long long a, long long b) {
#if defined(__SIZEOF_INT128__)
    __int128 prod = ( __int128 )a * ( __int128 )b;
    return prod > LLONG_MAX;
#else
    // Fallback for environments without __int128, valid for non-negative a,b
    if (a == 0 || b == 0) return false;
    return a > LLONG_MAX / b;
#endif
}

static string shortString(const string &s, int keep = 25) {
    if ((int)s.size() <= 2 * keep + 3) return s;
    return s.substr(0, keep) + " ... " + s.substr((int)s.size() - keep);
}

// ============================================================
// Formatting exact/approx results
// ============================================================

static void printBigProductInfo(const string &a, const string &b, const string &exactProduct) {
    cout << "  BigInt exact product digits = " << exactProduct.size() << "\n";
    if ((int)exactProduct.size() <= 120) {
        cout << "  BigInt exact product       = " << exactProduct << "\n";
    } else {
        cout << "  BigInt exact product       = " << shortString(exactProduct, 35) << "\n";
    }
}

static void demoCase(const string &label, const string &sa, const string &sb, bool showKaratsubaCheck = true) {
    cout << "============================================================\n";
    cout << label << "\n";
    cout << "A = " << shortString(sa, 35) << "\n";
    cout << "B = " << shortString(sb, 35) << "\n";

    // ---- int
    {
        bool fitsIntA = false, fitsIntB = false;
        long long tmpA = 0, tmpB = 0;

        if (fitsLongLongStringNonNegative(sa)) {
            tmpA = parseLLChecked(sa);
            fitsIntA = (tmpA <= INT_MAX);
        }
        if (fitsLongLongStringNonNegative(sb)) {
            tmpB = parseLLChecked(sb);
            fitsIntB = (tmpB <= INT_MAX);
        }

        cout << "  [int] ";
        if (!fitsIntA || !fitsIntB) {
            cout << "cannot even store operand(s) in int\n";
        } else {
            long long prod = tmpA * tmpB; // safe in long long for check
            if (prod > INT_MAX) {
                cout << "operands fit, but multiplication would overflow int\n";
            } else {
                cout << "safe, result = " << (int)prod << "\n";
            }
        }
    }

    // ---- long long
    {
        cout << "  [long long] ";
        if (!fitsLongLongStringNonNegative(sa) || !fitsLongLongStringNonNegative(sb)) {
            cout << "cannot even store operand(s) in long long\n";
        } else {
            long long a = parseLLChecked(sa);
            long long b = parseLLChecked(sb);
            if (willOverflowLLMulNonNegative(a, b)) {
                cout << "operands fit, but multiplication would overflow long long\n";
            } else {
                cout << "safe, result = " << (a * b) << "\n";
            }
        }
    }

    // ---- unsigned long long
    {
        cout << "  [unsigned long long] ";
        if (!fitsUnsignedLongLongString(sa) || !fitsUnsignedLongLongString(sb)) {
            cout << "cannot even store operand(s) in unsigned long long\n";
        } else {
            unsigned long long a = parseULLChecked(sa);
            unsigned long long b = parseULLChecked(sb);
            if (willOverflowULLMul(a, b)) {
                unsigned long long wrapped = a * b; // defined modulo 2^64
                cout << "operands fit, but result wraps modulo 2^64\n";
                cout << "                     wrapped result = " << wrapped << "\n";
            } else {
                cout << "safe, result = " << (a * b) << "\n";
            }
        }
    }

    // ---- double
    {
        cout << "  [double] ";
        try {
            double da = stod(sa);
            double db = stod(sb);
            double prod = da * db;

            if (isinf(prod)) {
                cout << "overflow to +inf\n";
            } else {
                cout << scientific << setprecision(17);
                cout << "approx result = " << prod << "\n";
                cout << defaultfloat;
            }
        } catch (const exception &) {
            cout << "number too large to parse into double exactly/at all\n";
        }
    }

    // ---- BigInt exact
    BigInt A = fromString(sa);
    BigInt B = fromString(sb);

    BigInt P1 = schoolbookMultiply(A, B);
    string exact1 = toString(P1);

    printBigProductInfo(sa, sb, exact1);

    if (showKaratsubaCheck) {
        BigInt P2 = karatsuba(A, B);
        string exact2 = toString(P2);
        cout << "  Karatsuba == Schoolbook ? "
             << (exact1 == exact2 ? "YES" : "NO") << "\n";
    }

    cout << "\n";
}

// ============================================================
// Benchmark
// ============================================================

static string randomDigits(int len, mt19937 &rng) {
    uniform_int_distribution<int> firstDigit(1, 9), otherDigit(0, 9);
    string s;
    s.reserve(len);
    s.push_back(char('0' + firstDigit(rng)));
    for (int i = 1; i < len; ++i) {
        s.push_back(char('0' + otherDigit(rng)));
    }
    return s;
}

static void benchmarkBigInt() {
    cout << "============================================================\n";
    cout << "BENCHMARK: Schoolbook vs Karatsuba on BigInt\n";
    cout << "(times vary by machine/compiler/optimization)\n\n";

    mt19937 rng(123456);
    vector<int> digitSizes = {50, 100, 200, 500, 1000, 2000};

    cout << left
         << setw(10) << "digits"
         << setw(20) << "schoolbook(ms)"
         << setw(20) << "karatsuba(ms)"
         << setw(12) << "match"
         << "\n";

    for (int digits : digitSizes) {
        string s1 = randomDigits(digits, rng);
        string s2 = randomDigits(digits, rng);

        BigInt a = fromString(s1);
        BigInt b = fromString(s2);

        auto t1 = chrono::high_resolution_clock::now();
        BigInt r1 = schoolbookMultiply(a, b);
        auto t2 = chrono::high_resolution_clock::now();
        BigInt r2 = karatsuba(a, b);
        auto t3 = chrono::high_resolution_clock::now();

        double schoolMs = chrono::duration<double, milli>(t2 - t1).count();
        double karaMs   = chrono::duration<double, milli>(t3 - t2).count();

        cout << left
             << setw(10) << digits
             << setw(20) << fixed << setprecision(3) << schoolMs
             << setw(20) << fixed << setprecision(3) << karaMs
             << setw(12) << (toString(r1) == toString(r2) ? "YES" : "NO")
             << "\n";
    }

    cout << "\n";
}

// ============================================================
// Main
// ============================================================

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    cout << "C++ MULTIPLICATION DEMO\n";
    cout << "Built-in types vs BigInt Schoolbook vs Karatsuba\n\n";

    cout << "Limits:\n";
    cout << "  INT_MAX                = " << INT_MAX << "\n";
    cout << "  LLONG_MAX              = " << LLONG_MAX << "\n";
    cout << "  ULLONG_MAX             = " << ULLONG_MAX << "\n";
    cout << "  DBL_MAX                = " << scientific << DBL_MAX << defaultfloat << "\n\n";

    // Small examples
    demoCase("Example 1: int overflow example", "50000", "50000");
    demoCase("Example 2: another int overflow example", "100000", "100000");
    demoCase("Example 3: safe in long long", "1000000000", "1000000000");

    // Near long long boundary
    demoCase("Example 4: still fits in long long multiplication", "3037000499", "3037000499");
    demoCase("Example 5: just above long long multiplication limit", "3037000500", "3037000500");

    // Unsigned wrap-around
    demoCase("Example 6: fits operands in unsigned long long, but product wraps", "10000000000", "10000000000");

    // User-like big numbers
    demoCase("Example 7: 20-digit numbers (cannot be handled exactly by built-in integer types)",
             "12345678901234567890",
             "98765432109876543210");

    // Very large / super large
    demoCase("Example 8: 100-digit numbers",
             string(100, '9'),
             string(100, '8'),
             false);

    demoCase("Example 9: 300-digit numbers",
             "1" + string(299, '0'),
             "9" + string(299, '9'),
             false);

    // Floating-point overflow example
    cout << "============================================================\n";
    cout << "Extra floating-point example\n";
    {
        double x = 1e200;
        double y = 1e200;
        double z = x * y;
        cout << "  x = 1e200, y = 1e200\n";
        cout << "  x * y = ";
        if (isinf(z)) cout << "+inf\n";
        else cout << scientific << setprecision(17) << z << defaultfloat << "\n";
        cout << "  -> double can represent a huge range, but not arbitrary exact integers,\n";
        cout << "     and very large multiplication can overflow to infinity.\n\n";
    }
    benchmarkBigInt();

    cout << "Summary:\n";
    cout << "  - int / long long: exact but very limited range.\n";
    cout << "  - unsigned long long: exact in range, overflow wraps modulo 2^64.\n";
    cout << "  - double: huge range but not exact for large integers.\n";
    cout << "  - BigInt schoolbook: exact, O(n^2).\n";
    cout << "  - BigInt karatsuba: exact, asymptotically faster, O(n^1.585).\n";

    return 0;
}