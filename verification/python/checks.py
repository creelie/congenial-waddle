"""Independent checks in Python (standard library only).

1. Gaussian binomial counts used by the C programs.
2. The five-dimensional space {[[a,0,b],[0,c-d-e,c],[b,d,e]]} over F_3 has no nonzero nilpotent.
3. For n = 2 and every prime q <= 7, and for n = 3 and q = 2, Conjecture 8 holds (an example is
   found), so the failure at n = 3, q = 3 is not an artefact of the tests.
4. Random six-dimensional subspaces of M_3(F_3): each contains a nonzero nilpotent (spot check of
   the exhaustive C search, by a different method: enumerate the subspace and cube every element).
5. Over F_3 the trace-zero matrices satisfy c2(X + aI) = c2(X) and det(X + aI) = det X + a^3 + a c2(X).
6. The six-dimensional examples of the paper over F_2 and F_5 have no nonzero nilpotent, and exactly
   128 of the 3x6 matrices C over F_2 give a nilpotent-free space {X_C(y)}.
"""
import itertools
import random


def gauss_binom(n, k, q):
    num = den = 1
    for i in range(k):
        num *= q ** (n - i) - 1
        den *= q ** (i + 1) - 1
    return num // den


def mul(a, b, q, n):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(n)) % q for j in range(n)) for i in range(n))


def is_nilpotent(x, q, n):
    p = x
    for _ in range(n - 1):
        p = mul(p, x, q, n)
    return all(v == 0 for row in p for v in row)


def span_elements(basis, q, n):
    for coeffs in itertools.product(range(q), repeat=len(basis)):
        if not any(coeffs):
            continue
        yield tuple(tuple(sum(c * b[i][j] for c, b in zip(coeffs, basis)) % q for j in range(n))
                    for i in range(n))


def nil_free(basis, q, n):
    for x in span_elements(basis, q, n):
        if all(v == 0 for row in x for v in row):
            return False  # dependent
        if is_nilpotent(x, q, n):
            return False
    return True


def random_subspace(dim, q, n, rng):
    while True:
        basis = [tuple(tuple(rng.randrange(q) for _ in range(n)) for _ in range(n)) for _ in range(dim)]
        if all(any(v for row in x for v in row) for x in span_elements(basis, q, n)):
            return basis


def main():
    assert gauss_binom(9, 3, 3) == 678468820
    assert gauss_binom(8, 3, 3) == 25095280
    assert gauss_binom(8, 4, 3) == 75913222
    print("1. Gaussian binomials: ok")

    bad = 0
    for a, b, c, d, e in itertools.product(range(3), repeat=5):
        if (a, b, c, d, e) == (0, 0, 0, 0, 0):
            continue
        x = ((a, 0, b), (0, (c - d - e) % 3, c), (b, d, e))
        bad += is_nilpotent(x, 3, 3)
    assert bad == 0
    print("2. five-dimensional example over F_3 has no nonzero nilpotent: ok")

    rng = random.Random(2026)
    for n, q in [(2, 2), (2, 3), (2, 5), (2, 7), (3, 2)]:
        dim = n * (n + 1) // 2
        for trial in range(200000):
            basis = random_subspace(dim, q, n, rng)
            if nil_free(basis, q, n):
                print(f"3. n={n}, q={q}: nilpotent-free subspace of dimension {dim} found (trial {trial})")
                break
        else:
            raise SystemExit(f"no example for n={n}, q={q}")

    for _ in range(3000):
        basis = random_subspace(6, 3, 3, rng)
        assert not nil_free(basis, 3, 3)
    print("4. 3000 random six-dimensional subspaces of M_3(F_3) all contain a nonzero nilpotent: ok")

    def c2(x):
        return (x[0][0] * x[1][1] - x[0][1] * x[1][0] + x[0][0] * x[2][2] - x[0][2] * x[2][0]
                + x[1][1] * x[2][2] - x[1][2] * x[2][1]) % 3

    def det(x):
        return (x[0][0] * (x[1][1] * x[2][2] - x[1][2] * x[2][1])
                - x[0][1] * (x[1][0] * x[2][2] - x[1][2] * x[2][0])
                + x[0][2] * (x[1][0] * x[2][1] - x[1][1] * x[2][0])) % 3

    for _ in range(20000):
        x = [[rng.randrange(3) for _ in range(3)] for _ in range(3)]
        x[2][2] = (-x[0][0] - x[1][1]) % 3
        for a in range(3):
            y = [[(x[i][j] + (a if i == j else 0)) % 3 for j in range(3)] for i in range(3)]
            assert c2(y) == c2(x)
            assert det(y) == (det(x) + a ** 3 + a * c2(x)) % 3
    print("5. shift identities for trace-zero matrices over F_3: ok")

    def x_c(c, y, q):
        u = [sum(c[r][j] * y[j] for j in range(6)) % q for r in range(3)]
        return ((y[0], -u[0] % q, -u[1] % q), (y[3], y[1], -u[2] % q), (y[4], y[5], y[2]))

    def graph_nil_free(c, q):
        return not any(is_nilpotent(x_c(c, y, q), q, 3)
                       for y in itertools.product(range(q), repeat=6) if any(y))

    c2_example = [[0, 1, 0, 1, 1, 0], [1, 0, 0, 0, 1, 1], [0, 1, 0, 0, 0, 1]]
    c5_example = [[2, 1, 0, 4, 3, 3], [2, 2, 0, 0, 2, 2], [4, 1, 4, 2, 0, 2]]
    assert graph_nil_free(c2_example, 2) and graph_nil_free(c5_example, 5)
    count = sum(graph_nil_free([[bits >> (6 * r + j) & 1 for j in range(6)] for r in range(3)], 2)
                for bits in range(1 << 18))
    assert count == 128, count
    print("6. examples over F_2 and F_5 are nilpotent-free; 128 nilpotent-free spaces over F_2: ok")


if __name__ == "__main__":
    main()
