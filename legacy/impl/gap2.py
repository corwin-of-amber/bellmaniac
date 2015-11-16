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

n = 16
w = [[random.randint(0, 100) for j in range(n+1)] for i in range(n)]
w1 = [[random.randint(0, 100) for j in range(n+1)] for i in range(n)]
S = [[random.randint(0, 100) for j in range(n+1)] for i in range(n+1)]

zero = 1000000000000000000000000
plus = min


# important to know what the output of the algorithm is to optimize
# for space
@memoize
def G(i, j):
  assert i <= n and j <= n
  if i == 0 and j == 0:
    return 0
  elif i == 0 and j > 0:
    return w[0][j]
  elif i > 0 and j == 0:
    return w1[0][i]
  else:
    return reduce(plus,
        [G(i, q) + w[q][j] for q in range(j)] +
        [G(p, j) + w1[p][i] for p in range(i)] +
        [G(i-1, j-1) + S[i][j]])

# Expanded version of G with an additional dimension for the list comprehension
@memoize
def G2(i, j, k = None):  
  if k == None:
    k = i + j

  if i == 0 and j == 0:
    return 0
  elif i == 0 and j > 0:
    return w[0][j]
  elif j == 0 and i > 0:
    return w1[0][i]
  elif k == 0:
    return G2(i-1, j-1) + S[i][j]
  elif k <= j:
    q = k - 1
    return plus(G2(i, j, k-1), G2(i, q) + w[q][j])
  elif k <= i + j:
    p = k - j - 1
    return plus(G2(i, j, k-1), G2(p, j) + w1[p][i])
   
# Parametrize by n, add initial values R
# oi, oj to reference constants w, w1, S
@memoize
def A1(i, j, n, R, oi, oj):
  assert i <= n and j <= n
  if i == 0 or j == 0:
    return R(i, j)
  else:
    return reduce(plus,
        [A1(i, q, n, R, oi, oj) + w[q+oj][j+oj] for q in range(j)] +
        [A1(p, j, n, R, oi, oj) + w1[p+oi][i+oi] for p in range(i)] +
        [A1(i-1, j-1, n, R, oi, oj) + S[i+oi][j+oj]],
        R(i, j))
# This is a part of A1 definition for the non-special case
@memoize
def B1(i, j, n, R, oi, oj, X):
  assert i <= n and j <= n
  
  if i == 0 or j == 0:
    return R(i, j)
  else:
    return reduce(plus,
        [X(i, q) + w[q+oj][j+oj] for q in range(n)],
        R(i, j))

# Partitioning scheme for A
# Define B and C problems
@memoize
def A2(i, j, n, R, oi, oj):
  assert i <= n and j <= n
  if n < 2:
    return A1(i, j, n, R, oi, oj)

  if i <= n/2 and j <= n/2:
    return A2(i, j, n/2, R, oi, oj)
  elif i > n/2 and j <= n/2:
    return A1(i, j, n, R, oi, oj)
  elif i <= n/2 and j > n/2:
    return A2(i, j-n/2, n/2, 
        lambda i0, j0: B1(i0, j0-n/2, n/2,
          lambda i, j: A1(i, j+n/2, n, R, oi, oj),
          oi, oj+n/2,
          lambda i, j: A2(i, j, n, R, oi, oj)),
        oi, oj+n/2)
  elif i > n/2 and j > n/2:
    return A1(i, j, n, R, oi, oj)

def R0(i, j):
  if i == 0 and j == 0:
    return 0
  elif i == 0 and j > 0:
    return w[0][j]
  elif i > 0 and j == 0:
    return w1[0][i]
  else:
    return zero

for i in range(n+1):
  for j in range(n+1):
    assert G(i, j) == G2(i, j)
    assert A1(i, j, n, R0, 0, 0) == G(i, j)
    assert A2(i, j, n, R0, 0, 0) == A1(i, j, n, R0, 0, 0)

print "OK"


