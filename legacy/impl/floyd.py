#!/usr/bin/python

import random
class memoize(dict):
  def __init__(self, func):
    self.func = func
  def __call__(self, *args):
     return self[args]
  def __missing__(self, key):
     result = self[key] = self.func(*key)
     return result

# n is a power of two
n = 16
w = [[random.randint(0, 100) for j in range(n)] for i in range(n)]

# closed semiring (monoid?)
zero = 100000000000000000
plus = min
times = lambda i, j: i + j
one = 0

x = random.randint(0, 100)
assert plus(x, zero) == x
assert times(x, one) == x

def l(i, j):
  if i == j:
    return one
  else:
    return w[i][j]

# Recurrence definition of d
@memoize
# i, j in range(n)
# k in [0,n]
# cost paths from i to j with intermediate vertices < k
def d(i, j, k):
  if k == 0:
    return l(i, j)
  else:
    return plus(d(i, j, k-1), times(d(i, k-1, k-1), d(k-1, j, k-1)))

print "d:"
for i in range(n):
  print [d(i, j, n) for j in range(n)]


# generalize initial values
@memoize
def A(i, j, k, n, R):
  if k == 0:
    return R(i, j)
  else:
    return plus(A(i, j, k-1, n, R), times(A(i, k-1, k-1, n, R), A(k-1, j, k-1, n, R)))
 
for i in range(n):
  for j in range(n):
    assert d(i, j, n) == A(i, j, n, n, l)

# partition based on i, j, k (not obvious from pictures)
# (total 8 partitions)
# handle simple case
# important to make sure i and j partitions are equal in size
def A1(i, j, k, n, R):
  assert i < n and j < n and k <= n
  if n < 2:
    return A(i, j, k, n, R)
  elif k == 0:
    return R(i, j)
  elif i < n/2 and j < n/2 and k <= n/2:
    return A(i, j, k, n, R)
  elif i < n/2 and j >= n/2 and k <= n/2:
    return A(i, j, k, n, R)      
  elif i >= n/2 and j < n/2 and k <= n/2:
    return A(i, j, k, n, R)
  elif i >= n/2 and j >= n/2 and k <= n/2:
    return A(i, j, k, n, R)
  elif i >= n/2 and j >= n/2 and k > n/2:
    return A(i, j, k, n, R)
  elif i < n/2 and j >= n/2 and k > n/2:
    return A(i, j, k, n, R)
  elif i >= n/2 and j < n/2 and k > n/2:
    return A(i, j, k, n, R)
  elif i < n/2 and j < n/2 and k > n/2:
    return A(i, j, k, n, R)

print "check A1"
for i in range(n):
  for j in range(n):
    for k in range(n+1):
      assert d(i, j, k) == A1(i, j, k, n, l)

# induction on n
# define B, C rigorously at this point
# for the partitions

# S can unify with another partition
def B(i, j, k, n, R, S):
  assert i < n/2 and j < n/2 and k <= n/2
  # (i, j) -> (k-1, j)
  if k == 0:
    return R(i, j)
  else:
    return plus(B(i, j, k-1, n, R, S), times(S(i, k-1, k-1), B(k-1, j, k-1, n, R, S)))

@memoize
def B1(i, j, k, n, R, S):
  assert i < n/2 and j < n/2 and k <= n/2
  # recursion (i, j) -> (k-1, j)
  if n < 4:
    return B(i, j, k, n, R, S)
  elif k == 0:
    return R(i, j)
  else:
    m = n/2;
    # partition into m-subproblems
    if i < m/2 and j < m/2 and k <= m/2:
      return B1(i, j, k, m, R, S)
    elif i < m/2 and j >= m/2 and k <= m/2:
      return B1(i, j-m/2, k, m, 
          lambda i, j: R(i, j+m/2),
          S)
    elif i >= m/2 and j < m/2 and k <= m/2:
      return D1(i-m/2, j, k, m, 
          lambda i, j: R(i+m/2, j),
          lambda i, j, k: B1(i, j, k, n, R, S),
          lambda i, j, k: S(i+m/2, j, k))
    elif i >= m/2 and j >= m/2 and k <= m/2:
      return D1(i-m/2, j-m/2, k, m,
          lambda i, j: R(i+m/2, j+m/2),
          lambda i, j, k: B1(i, j+m/2, k, n, R, S),
          lambda i, j, k: S(i+m/2, j, k))
    elif i >= m/2 and j < m/2 and k > m/2:
      return B1(i-m/2, j, k-m/2, m,
          lambda i, j: B1(i+m/2, j, m/2, n, R, S),
          lambda i, j, k: S(i+m/2, j+m/2, k+m/2))    
    elif i >= m/2 and j >= m/2 and k > m/2:
      return B1(i-m/2, j-m/2, k-m/2, m,
          lambda i, j: B1(i+m/2, j+m/2, m/2, n, R, S),
          lambda i, j, k: S(i+m/2, j+m/2, k+m/2))
    elif i < m/2 and j < m/2 and k > m/2:
      return D1(i, j, k-m/2, m,
          lambda i, j: B1(i, j, m/2, n, R, S),
          lambda i, j, k: B1(i+m/2, j, k+m/2, n, R, S),
          lambda i, j, k: S(i, j+m/2, k+m/2))
    elif i < m/2 and j >= m/2 and k > m/2:
      return D1(i, j-m/2, k-m/2, m,
          lambda i, j: B1(i, j+m/2, m/2, n, R, S),
          lambda i, j, k: B1(i+m/2, j+m/2, k+m/2, n, R, S),
          lambda i, j, k: S(i, j+m/2, k+m/2))

# S can unify with another partition
def C(i, j, k, n, R, S):
  assert i < n/2 and j < n/2 and k <= n/2
  # (i, j) -> (i, k-1)
  if k == 0:
    return R(i, j)
  else:
    return plus(C(i, j, k-1, n, R, S), times(C(i, k-1, k-1, n, R, S), S(k-1, j, k-1)))

# TODO: finish the algorithm
@memoize
def C1(i, j, k, n, R, S):
  return C(i, j, k, n, R, S)


# S, T can unify with two partitions
def D(i, j, k, n, R, S, T):
  assert i < n/2 and j < n/2 and k <= n/2
  # (i, j) -> (i, j)
  if k == 0:
    return R(i, j)
  else:
    return plus(D(i, j, k-1, n, R, S, T), times(T(i, k-1, k-1), S(k-1, j, k-1)))

# TODO: finish the algorithm for this one
@memoize
def D1(i, j, k, n, R, S, T):
  return D(i, j, k, n, R, S, T)

@memoize
def A2(i, j, k, n, R):
  assert i < n and j < n and k <= n, "i=%s, j=%s, k=%s, n=%s" % (i, j, k, n)
  # must have well-ordering on the induction parameters

  # These cases should be executed in sequence and stored in an array 
  # to avoid recomputation
  if n < 2:
    return A(i, j, k, n, R)
  elif k == 0:
    return R(i, j)
  elif i < n/2 and j < n/2 and k <= n/2:
    # 1) n decreases 
    # simple reduction
    return A2(i, j, k, n/2, R)
  elif i < n/2 and j >= n/2 and k <= n/2:
    # 2) calls A2 with j < n/2 -> 1)    
    # B reduction
    return B1(i, j-n/2, k, n, 
        lambda i, j: R(i, j+n/2), 
        lambda i, j, k: A2(i, j, k, n, R)) 
  elif i >= n/2 and j < n/2 and k <= n/2:
    # 3) calls A2 with i < n/2 -> 1)
    # C reduction     
    return C1(i-n/2, j, k, n, 
        lambda i, j: R(i+n/2, j), 
        lambda i, j, k: A2(i, j, k, n, R)) 
  elif i >= n/2 and j >= n/2 and k <= n/2:
    # 4) calls A2 with (k-1, j+n/2, k-1) and (i+n/2, k-1, k-1) -> 2) and 3)
    # D reduction
    return D1(i-n/2, j-n/2, k, n, 
        lambda i, j: R(i+n/2, j+n/2), 
        lambda i, j, k: A2(i, j+n/2, k, n, R), 
        lambda i, j, k: A2(i+n/2, j, k, n, R)) 
  elif i >= n/2 and j >= n/2 and k > n/2:
    # 5) calls A2 with (i+n/2, j+n/2, n/2) -> 4)
    # A with pre-computed initial state   
    # non-trivial proof here
    return A2(i-n/2, j-n/2, k-n/2, n/2, 
        lambda i, j: A2(i+n/2, j+n/2, n/2, n, R))        
  elif i < n/2 and j >= n/2 and k > n/2:   
    # 6) calls A2 with (k-1+n/2, j+n/2, k-1+n/2) and (i, j+n/2, n/2) -> 5) and 2)
    return C1(i, j-n/2, k-n/2, n, 
        lambda i, j: A2(i, j+n/2, n/2, n, R),
        lambda i, j, k: A2(i+n/2, j+n/2, k+n/2, n, R))
  elif i >= n/2 and j < n/2 and k > n/2:
    # 7) calls A2 with (i+n/2, k-1+n/2, k-1+n/2) and (i+n/2, j, n/2) -> 5) and 3)
    return B1(i-n/2, j, k-n/2, n,
        lambda i, j: A2(i+n/2, j, n/2, n, R),
        lambda i, j, k: A2(i+n/2, j+n/2, k+n/2, n, R))
  elif i < n/2 and j < n/2 and k > n/2:
    # 8) calls A2 with (k-1+n/2, j, k-1+n/2), (i, k-1+n/2, k-1+n/2), (i, j, n/2) -> 6), 7), 1)
    return D1(i, j, k-n/2, n,
        lambda i, j: A2(i, j, n/2, n, R),
        lambda i, j, k: A2(i+n/2, j, k+n/2, n, R),
        lambda i, j, k: A2(i, j+n/2, k+n/2, n, R))

print "check A2"
for i in range(n):
  for j in range(n):
    for k in range(n+1):
      assert d(i, j, k) == A2(i, j, k, n, l)



