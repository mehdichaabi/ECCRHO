# -*- coding: utf-8 -*-
"""
Created on Thu Dec  6 18:57:52 2018

@author: Dell
"""

import random



class EllipticCurve:
    """An elliptic curve over a prime field.
    The field is specified by the parameter 'p'.
    The curve coefficients are 'a' and 'b'.
    The base point of the cyclic subgroup is 'g'.
    The order of the subgroup is 'n'.
    """

    def __init__(self, p, a, b, g, n):
        self.p = p
        self.a = a
        self.b = b
        self.g = g
        self.n = n

        assert pow(2, p - 1, p) == 1
        assert (4 * a * a * a + 27 * b * b) % p != 0
        assert self.is_on_curve(g)
        assert self.mult(n, g) is None

    def is_on_curve(self, point):
        """Checks whether the given point lies on the elliptic curve."""
        if point is None:
            return True

        x, y = point
        return (y * y - x * x * x - self.a * x - self.b) % self.p == 0

    def add(self, point1, point2):
        """Returns the result of point1 + point2 according to the group law."""
        assert self.is_on_curve(point1)
        assert self.is_on_curve(point2)

        if point1 is None:
            return point2
        if point2 is None:
            return point1

        x1, y1 = point1
        x2, y2 = point2

        if x1 == x2 and y1 != y2:
            return None

        if x1 == x2:
            m = (3 * x1 * x1 + self.a) * inverse_mod(2 * y1, self.p)
        else:
            m = (y1 - y2) * inverse_mod(x1 - x2, self.p)

        x3 = m * m - x1 - x2
        y3 = y1 + m * (x3 - x1)
        result = (x3 % self.p,
                  -y3 % self.p)

        assert self.is_on_curve(result)

        return result

    def double(self, point):
        """Returns 2 * point."""
        return self.add(point, point)

    def neg(self, point):
        """Returns -point."""
        if point is None:
            return None

        x, y = point
        result = x, -y % self.p

        assert self.is_on_curve(result)

        return result

    def mult(self, n, point):
        """Returns n * point computed using the double and add algorithm."""
        if n % self.n == 0 or point is None:
            return None

        if n < 0:
            return self.neg(self.mult(-n, point))

        result = None
        addend = point

        while n:
            if n & 1:
                result = self.add(result, addend)
            addend = self.double(addend)
            n >>= 1

        return result

    def __str__(self):
        a = abs(self.a)
        b = abs(self.b)
        a_sign = '-' if self.a < 0 else '+'
        b_sign = '-' if self.b < 0 else '+'

        return 'y^2 = (x^3 {} {}x {} {}) mod {}'.format(
            a_sign, a, b_sign, b, self.p)


def inverse_mod(n, p):
    """Returns the inverse of n modulo p.
    This function returns the only integer x such that (x * n) % p == 1.
    n must be non-zero and p must be a prime.
    """
    if n == 0:
        raise ZeroDivisionError('division by zero')
    if n < 0:
        return p - inverse_mod(-n, p)

    s, old_s = 0, 1
    t, old_t = 1, 0
    r, old_r = p, n

    while r != 0:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_s - quotient * t

    gcd, x, y = old_r, old_s, old_t

    assert gcd == 1
    assert (n * x) % p == 1

    return x % p

curve = EllipticCurve(
    p=10177,
    a=1,
    b=-1,
    g=(1, 1),
    n=10331,
)



class PollardRhoSequence:

    def __init__(self, point1, point2):
        self.point1 = point1
        self.point2 = point2

        self.add_a1 = random.randrange(1, curve.n)
        self.add_b1 = random.randrange(1, curve.n)
        self.add_x1 = curve.add(
            curve.mult(self.add_a1, point1),
            curve.mult(self.add_b1, point2),
        )

        self.add_a2 = random.randrange(1, curve.n)
        self.add_b2 = random.randrange(1, curve.n)
        self.add_x2 = curve.add(
            curve.mult(self.add_a2, point1),
            curve.mult(self.add_b2, point2),
        )

    def __iter__(self):
        partition_size = curve.p // 3 + 1

        x = None
        a = 0
        b = 0

        while True:
            if x is None:
                i = 0
            else:
                i = x[0] // partition_size

            if i == 0:
                # x is either the point at infinity (None), or is in the first
                # third of the plane (x[0] <= curve.p / 3).
                a += self.add_a1
                b += self.add_b1
                x = curve.add(x, self.add_x1)
            elif i == 1:
                # x is in the second third of the plane
                # (curve.p / 3 < x[0] <= curve.p * 2 / 3).
                a *= 2
                b *= 2
                x = curve.double(x)
            elif i == 2:
                # x is in the last third of the plane (x[0] > curve.p * 2 / 3).
                a += self.add_a2
                b += self.add_b2
                x = curve.add(x, self.add_x2)
            else:
                raise AssertionError(i)

            a = a % curve.n
            b = b % curve.n

            yield x, a, b


def log(p, q, counter=None):
    assert curve.is_on_curve(p)
    assert curve.is_on_curve(q)

    # Pollard's Rho may fail sometimes: it may find a1 == a2 and b1 == b2,
    # leading to a division by zero error. Because PollardRhoSequence uses
    # random coefficients, we have more chances of finding the logarithm
    # if we try again, without affecting the asymptotic time complexity.
    # We try at most three times before giving up.
    for i in range(3):
        sequence = PollardRhoSequence(p, q)

        tortoise = iter(sequence)
        hare = iter(sequence)

        # The range is from 0 to curve.n - 1, but actually the algorithm will
        # stop much sooner (either finding the logarithm, or failing with a
        # division by zero).
        for j in range(curve.n):
            x1, a1, b1 = next(tortoise)

            x2, a2, b2 = next(hare)
            x2, a2, b2 = next(hare)

            if x1 == x2:
                if b1 == b2:
                    # This would lead to a division by zero. Try with
                    # another random sequence.
                    break

                x = (a1 - a2) * inverse_mod(b2 - b1, curve.n)
                logarithm = x % curve.n
                steps = i * curve.n + j + 1
                return logarithm, steps

    raise AssertionError('logarithm not found')


def main():
    x = random.randrange(1, curve.n)
    p = curve.g
    q = curve.mult(x, p)

    print('Curve: {}'.format(curve))
    print('Curve order: {}'.format(curve.n))
    print('p = (0x{:x}, 0x{:x})'.format(*p))
    print('q = (0x{:x}, 0x{:x})'.format(*q))
    print(x, '* p = q')

    y, steps = log(p, q)
    print('log(p, q) =', y)
    print('Took', steps, 'steps')

    assert x == y


if __name__ == '__main__':
    main()