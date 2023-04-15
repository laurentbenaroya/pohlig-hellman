
from functools import reduce
from gmpy2 import invert, isqrt, powmod, gcd, lcm
from factordb.factordb import FactorDB


"""
prime factor decomposition tool based on factprdb
"""

def integer2factordict(N, verbose=False):
    """
    get factors and put them in a dictionary, i.e.
    if N = 2*2*3*3*3*3*5*7*7
    then the output will be {2: 2, 3: 4, 5: 1, 7: 2}
    REM : factordb needs a connection to internet
    """
    f = FactorDB(N)
    f.connect()
    factors = f.get_factor_list()
    f.get_status()
    # build dictonary
    factors_dict = dict()
    for f in factors:
        if f not in factors_dict:
            factors_dict[f] = 1
        else:
            factors_dict[f] += 1
    if verbose:
        print(f'numbers of primes {len(factors_dict)}')
        print(f'factor decompistion :')
        for k, v in factors_dict.items():
            print(f'{k} : {v}')
    return factors_dict


def chinese_remainder_theorem(a, m):
    """
    Solves the system of linear congruences:
        x = a[0] (mod m[0])
        x = a[1] (mod m[1])
        ...
        x = a[n-1] (mod m[n-1])
    using the Chinese Remainder Theorem.
    """
    # Check that all moduli are pairwise coprime
    n = len(m)
    for i in range(n):
        for j in range(i+1, n):
            if gcd(m[i], m[j]) != 1:
                return None
    # Compute the product of all moduli
    M = 1
    for k in m:
        M *= k
    # Compute the solution x using the CRT formula
    x = 0
    for i in range(n):
        Mi = M // m[i]
        Mi_inv = invert(Mi, m[i])
        x += a[i] * Mi * Mi_inv
    return x % M


def baby_step_giant_step(g, h, p, q, verbose=False):
    """
    find x such as pow(g, h, p) = b
    """
    m = isqrt(q - 1) + 1

    # Compute table of a^j (mod m) for j = 0, 1, ..., n-1
    if verbose:
        print(f'Compute table of a^j (mod m) for j = 0, 1, ..., n-1')
    table = {}
    # for j in tqdm.tqdm(range(m), total=int(m)):
    for j in range(m):
        table[powmod(g, j, p)] = j

    # Compute value of a^(n * (m-2)) (mod m)
    if verbose:
        print('Compute value of g^(m * (p-2)) (mod p)')
    gn = powmod(g, m * (p - 2), p)
    # currentPower = (gn * h) % p
    # Search for a match between b * a^(-kj) (mod m) and table
    if verbose:
        print(f'Search for a match between h * g^(-kj) (mod m) and table')
    y = h % p
    # for k in tqdm.tqdm(range(m), total=int(m)):
    for k in range(m):  
        # y = (h * powmod(gn, k, p)) % p
        if y in table:
            return m * k + table[y]
        y = (y*gn) % p
    return None


def discrete_log_power_prime(g, h, p, e, ptot):
    """
    g : generator
    h : 
    p : prime
    e : exponent
    the group is cyclic of order p**e
    """
    n = p**e
    ginv = invert(g, ptot)
    gamma = powmod(g, p**(e-1), ptot)
    xk = 0
    for k in range(e):
        hk = powmod(powmod(ginv, xk, ptot)*h, p**(e-1-k), ptot)
        dk = baby_step_giant_step(gamma, hk, ptot, n, verbose=False)
        xk += dk*p**k
    return xk


def pohlig_hellman_wikipedia(h, g, p):   # log_g(h) % p
    """
    https://www.wikiwand.com/en/Pohlig%E2%80%93Hellman_algorithm or https://en.wikipedia.org/wiki/Pohlig%E2%80%93Hellman_algorithm
    note that all powmod are taken modulo p not q to some power
    also the case q == 2 is handled separately, using brute force
    """
    factordict = integer2factordict(p-1)
    factorlist = [q**e for q, e in factordict.items()]
    # print(factorlist)
    loglist = []
    
    for q, e in factordict.items():

        qe = q**e
        gi = powmod(g, (p-1)//qe, p)
        hi = powmod(h, (p-1)//qe, p)
        if q == 2:
            found = False
            for x in range(q**e):
                if powmod(gi, x, p) == hi:
                    found = True
                    break
            if not found:
                raise Exception(f'error in DL with q = 2 and e = {e}, gi = {gi}, hi = {hi}, p = {p}')
        else:
            x = discrete_log_power_prime(gi, hi, q, e, p)
        loglist.append(x)

    # print(loglist)
    return chinese_remainder_theorem(loglist, factorlist)


def is_primitive_root(n, p):
    if gcd(n, p) != 1:
        return False
    factordict = integer2factordict(p-1)
    for factor in factordict.keys():
        if powmod(n, (p-1) // factor, p) == 1:
            return False
    return True


def get_order(n, p):
    factordict = integer2factordict(p-1)
    ordern = p-1
    for q, e in factordict.items():
        # find exponent oexp such that powmod(n, (p-1)//(q**oexp), 1) == 1
        oexp = 1
        for l in range(e):
            if powmod(n, (p-1)// (q**l), p) == 1:
                oexp *= q
        # update order of n
        ordern = ordern // oexp
    return ordern


def multiplicative_order_prime_power(n, r):
    # https://rosettacode.org/wiki/Multiplicative_order#Python
    # thanks rosetta code!    
    p, e = r
    m = p**e
    t = (p-1)*(p**(e-1)) #  = Phi(p**e) where p prime
    qs = [1,]
    for f in integer2factordict(t).items():
        qs = [q*f[0]**j for j in range(1+f[1]) for q in qs]
    qs.sort()

    for q in qs:
        if pow(n, q, m)==1: 
            break
    return q


def multiplicative_order(n, p):
    # https://rosettacode.org/wiki/Multiplicative_order#Python
    # thanks rosetta code!
    if gcd(n, p) != 1:
        return None
    factordict = integer2factordict(p)
    mofs = (multiplicative_order_prime_power(n, r) for r in factordict.items())
    return reduce(lcm, mofs, 1)  # lcm over all mofs
    

def test(g, h, p, testnum):
    """
    run Pohlig-Hellman
    """
    print('test %d' % testnum)
    isprimitiveroot = is_primitive_root(g, p)
    print(f'{g} is a primitive root modulo {p} ? : {isprimitiveroot}')

    print(f'{g} ** x = {h} mod {p}')
    x = pohlig_hellman_wikipedia(h, g, p)

    if isprimitiveroot:
        print(f'x = {x}')
        is_solution = powmod(g, x, p) == h
        print('x is a solution ? : ', is_solution)
    else:
        orderg = multiplicative_order_prime_power(g, (p, 1))
        print('multiple solutions')
        print(f'order of {g} mod {p} = {orderg}')
        
        for k in range((p-1)//orderg):
            xo = (x+k*orderg) % (p-1)
            print('solution number %d' % (k+1))
            print(f'x = {xo}')
            is_solution = powmod(g, xo, p) == h
            print('x is a solution ? : ', is_solution)
            print()            
    print()


if __name__ == '__main__':

    print('Pohlig Hellman')
    
    p = 16007670376277647657
    g = 2
    h = 4036795270454117606
    test(g, h, p, 1)

    M = 424242
    g, h, p = 5, M, 368585361623
    test(g, h, p, 2)

    g, h, p = 7, 385, 401  # not a safe prime
    test(g, h, p, 3)

    g, h, p = 2, 39183497, 41022299
    test(g, h, p, 4)
