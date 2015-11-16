#!/usr/bin/python
import random

# Goal: get rid of the state -- use stateless mutually recursive functions throughout
# Generalization steps:
# -- introducing new parameters (to allow unification with the sub-problem), finding the right initial values
# -- splitting into new sub-problems (B and C)
# -- partitioning the domain (A, B, and C)

# Need: 
# -- abstractions to express partitioning easier
# -- monoid formulation

n = 16
w = [[random.randint(0, 100) for j in range(n)] for i in range(n)]

print "w:"
for i in range(n):
  print w[i]

Infinity = 1000000000000000000000000

def Inf(i, j):
  if i == 0 and j == 0:
    return 0
  else:
    return Infinity

class memoize(dict):
  def __init__(self, func):
    self.func = func

  def __call__(self, *args):
    return self[args]

  def __missing__(self, key):
    result = self[key] = self.func(*key)
    return result

# assuming w is a distance metric
@memoize
def G(i, j):
  if i == 0 and j == 0:
    return 0
  else:
    return min(
      min([G(i, q) + w[q][j] for q in range(j)]) 
        if j > 0 else Infinity, 
      min([G(p, j) + w[i][p] for p in range(i)])
        if i > 0 else Infinity)


# n/2 problem recursion
# i,j in range(0, n/2)
def B1(i, j, oi, oj, n):
  return min([G1(i+oi, q+oj) + w[q+oj][j+oj+n/2] for q in range(n/2)])


# dj is the offset of the target cell, default n/2
# i, j in range(0, n/2)
def B2(i, j, oi, oj, n, dj):
  if n == 2:
    # Use A1 here?
    return G1(i+oi, oj) + w[oj][j+oj+dj]
  else:
    return min(
        B2(i, j, oi, oj, n/2, dj), 
        B2(i, j, oi, oj+n/4, n/2, dj-n/4))
        
# Lemma B1 = B2
    

# n/2 problem recursion
# i,j in range(0, n/2)
def C1(i, j, oi, oj, n):
  return min([G1(p+oi, j+oj) + w[i+oi+n/2][p+oi] for p in range(n/2)])

def C2(i, j, oi, oj, n, di):
  if n == 2:
    return G1(oi, j+oj) + w[i+oi+di][oi]
  else:
    return min(
        C2(i, j, oi, oj, n/2, di),
        C2(i, j, oi+n/4, oj, n/2, di-n/4))

# Lemma C1 = C2

# n/2 problem recursion
# i,j indeces are in range(n/2)
@memoize
def A(i, j, oi, oj, R, n):
  if i == 0 and j == 0:
    return R(i, j)
  else:
    return min(R(i, j),
      min([A(i, q, oi, oj, R, n) + w[q+oj][j+oj] for q in range(j)])
        if j > 0 else Infinity,
      min([A(p, j, oi, oj, R, n) + w[i+oi][p+oi] for p in range(i)])
        if i > 0 else Infinity)
 
def A1(i, j, oi, oj, R, n):
  if i == 0 and j == 0:
    return R(i, j)
  elif i < n/2 and j < n/2:
    return A1(i, j, oi, oj, R, n/2)
  elif i < n/2 and j >= n/2:
    return A1(i, j-n/2, oi, oj+n/2, 
      lambda i, j: min(R(i, j+n/2), B2(i, j, oi, oj, n, n/2)), n/2)
  elif i >= n/2 and j < n/2: 
    return A1(i-n/2, j, oi+n/2, oj,
      lambda i, j: min(R(i+n/2, j), C2(i, j, oi, oj, n, n/2)), n/2)
  else: 
    return A1(i-n/2, j-n/2, oi+n/2, oj+n/2,
      lambda i, j: min(R(i+n/2, j+n/2), B2(i, j, oi+n/2, oj, n, n/2), C2(i, j, oi, oj+n/2, n, n/2)), n/2)

# Lemma A = A1

@memoize
def G1(i, j):
  return A1(i, j, 0, 0, Inf, n)
    
print "G:"
for i in range(n):
  print [G(i,j) for j in range(n)]

print "G1:"
for i in range(n):
  print [G1(i,j) for j in range(n)]

for i in range(n):
  for j in range(n):
    assert G(i, j) == G1(i, j), 'error for %s and %s: %s and %s' % (i, j, G(i, j), G1(i, j))

