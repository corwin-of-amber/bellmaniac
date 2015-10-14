#!/usr/bin/python
import random
import sys
sys.setrecursionlimit(2 ** 16)

class memoize(dict):
  def __init__(self, func):
    self.func = func

  def __call__(self, *args):
    return self[args]

  def __missing__(self, key):
    result = self[key] = self.func(*key)
    return result

def shift(f, *v):
  def wrapped(*args):    
    return f(*tuple(x+y for x, y in zip(v, args)))
  return wrapped

plus = min
zero = 100000000000000000000000000000

n = 16
w = [[[random.randint(0, 100)
  for j in range(n)]
  for k in range(n)] 
  for i in range(n)]

x = [random.randint(0, 100) for i in range(n)]
      
@memoize
def c(i, j): 
  assert i < n and j < n and i < j
  if i == j-1:
    return x[j]
  else:
    return reduce(plus, 
        [c(i, k) + c(k, j) for k in range(i+1, j)] + 
        [w[i][k][j] for k in range(i+1, j)])

@memoize
# Offset o to reference x and w arrays
# Shortcut instead of making and passing lambdas for x and w
def A(i, j, n, o): 
  assert i < n and j < n and i < j
  if i == j-1:
    return x[j+o]
  else:
    return reduce(plus,
        [A(i, k, n, o) + A(k, j, n, o) for k in range(i+1, j)] + 
        [w[i+o][k+o][j+o] for k in range(i+1, j)])

for i in range(n):
  for j in range(i+1, n):
    assert c(i, j) == A(i, j, n, 0)

@memoize
# Partitioning scheme
def A1(i, j, n, o):
  assert i < n and j < n and i < j
  if n < 4:
    return A(i, j, n, o)
  
  if i < n/2 and j < n/2:
    return A1(i, j, n/2, o)
  elif i >= n/2 and j >= n/2:
    return A1(i-n/2, j-n/2, n/2, o+n/2)
  elif i < n/2 and j >= n/2:
    return A(i, j, n, o)

for i in range(n):
  for j in range(i+1, n):
    assert A(i, j, n, 0) == A1(i, j, n, 0)

# Define B problem
# Reference frame is in the black region
# We need the base case mask R as usual
# (note it's not just the lower-left value, but the entire region to make B-C split)
@memoize
def B(i, j, n, R, W, U, V):
  assert i < n/2 and j < n/2
  # explicit write down of the original definition
  # base case is explicitly passed in the recursion,
  # base case (i,j) is also resolved
  return reduce(plus,
    [U(i, k) + B(k, j, n, R, W, U, V) for k in range(i+1, n/2)] +   
    [B(i, k, n, R, W, U, V) + V(k, j) for k in range(0, j)] +
    [W(i, k, j+n/2) for k in range(i+1, j+n/2)],
    R(i, j))

@memoize
def C(i, j, n, R, W, U, V):
  assert i < n/2 and j < n/2
  return reduce(plus,
    [U(i, k) + V(k, j) for k in range(0, n/2)] + 
    [W(i, k, j) for k in range(0, n/2)],
    R(i, j))

@memoize
def C1(i, j, n, R, W, U, V):
  assert i < n/2 and j < n/2
  if n < 4:
    return C(i, j, n, R, W, U, V)

  # this is fairly standard partitioning (since C is not self-recursive)
  if i < n/4 and j < n/4:
    return C1(i, j, n/2, 
        lambda i, j: C1(i, j, n/2, R, W, U, V),
        shift(W, 0, n/4, 0),
        shift(U, 0, n/4),
        shift(V, n/4, 0))                  
  elif i >= n/4 and j < n/4:
    return C1(i-n/4, j, n/2, 
        lambda i, j: C1(i, j, n/2, 
          shift(R, n/4, 0),
          shift(W, n/4, 0, 0),
          shift(U, n/4, 0),
          V),
        shift(W, n/4, n/4, 0),
        shift(U, n/4, n/4),
        shift(V, n/4, 0))
  elif i < n/4 and j >= n/4:
    return C1(i, j-n/4, n/2,
        lambda i, j: C1(i, j, n/2,
          shift(R, 0, n/4),
          shift(W, 0, 0, n/4),
          U,
          shift(V, 0, n/4)),
        shift(W, 0, n/4, n/4),
        shift(U, 0, n/4),
        shift(V, n/4, n/4))
  elif i >= n/4 and j >= n/4:
    return C1(i-n/4, j-n/4, n/2,
        lambda i, j: C1(i, j, n/2,
          shift(R, n/4, n/4),
          shift(W, n/4, 0, n/4),
          shift(U, n/4, 0),
          shift(V, 0, n/4)),
        shift(W, n/4, n/4, n/4),
        shift(U, n/4, n/4),
        shift(V, n/4, n/4))

# Partitioning scheme for B
@memoize
def B1(i, j, n, R, W, U, V):
  assert i < n/2 and j < n/2
  if n < 4:
    return B(i, j, n, R, W, U, V)
    
  if i >= n/4 and j < n/4:
    return B1(i-n/4, j, n/2, 
        lambda i, j: R(i+n/4, j),
        lambda i, k, j: W(i+n/4, k+n/4, j+n/4), 
        lambda i, j: U(i+n/4, j+n/4),
        lambda i, j: V(i, j))
  elif i < n/4 and j < n/4:    
    return B1(i, j, n/2,
        lambda i, j: C1(i, j, n/2, 
          lambda i, j: R(i, j),
          lambda i, k, j: W(i, j+n/4+k, j+n/2),
          lambda i, j: U(i, j+n/4),
          lambda i, j: B1(i+n/4, j, n, R, W, U, V)),
        lambda i, k, j: W(i, k, j+n/4), # reads (i+1, j+n/4)
        lambda i, j: U(i, j),
        lambda i, j: V(i, j))
  elif i >= n/4 and j >= n/4:
    # i-n/4+1 to n/4: U(i, i+1...n/2) 
    # 0 to j-n/4: V(n/4...j, j)
    return B1(i-n/4, j-n/4, n/2,
        lambda i, j: C1(i, j, n/2,
          lambda i, j: R(i+n/4, j+n/4),
          lambda i, k, j: W(i+n/4, j+n/2+k, j+n/4+n/2),
          lambda i, j: B1(i+n/4, j, n, R, W, U, V), 
          lambda i, j: V(i, j+n/4)),
        # W(i, i...j+n/4, j+n/2)
        lambda i, k, j: W(i+n/4, k+n/4, j+n/2), # reads (i+1, j+n/4)
        lambda i, j: U(i+n/4, j+n/4),
        lambda i, j: V(i+n/4, j+n/4))
  elif i < n/4 and j >= n/4:
    # i+1 to n/4: U(i, i+1...n/4)
    # 0 to j-n/4: V(0 to j, j)
    # W domain is split into two parts between C subproblems 
    # (for now, equally)
    return B1(i, j-n/4, n/2, 
        lambda i, j: C1(i, j, n/2,
          lambda i, j: C1(i, j, n/2,
            lambda i, j: R(i, j+n/4),
            lambda i, k, j: W(i, j+n/2+k, j+n/4+n/2),
            lambda i, j: B1(i, j, n, R, W, U, V),
            lambda i, j: V(i, j+n/4)),
          lambda i, k, j: W(i, j+n/4+k, j+n/4+n/2),
          lambda i, j: U(i, j+n/4),
          lambda i, j: B1(i+n/4, j+n/4, n, R, W, U, V)),
        lambda i, k, j: W(i, k, j+n/2), # reads (i+1, j)
        lambda i, j: U(i, j),
        lambda i, j: V(i+n/4, j+n/4))

@memoize
def A2(i, j, n, o):
  assert i < n and j < n and i < j, "%d, %d, %d" % (i, j, n)
  if n < 4:
    return A(i, j, n, o)
  
  if i < n/2 and j < n/2:
    return A2(i, j, n/2, o)
  elif i >= n/2 and j >= n/2:
    return A2(i-n/2, j-n/2, n/2, o+n/2)
  elif i < n/2 and j >= n/2:    
    return B1(i, j-n/2, n,
        lambda i, j: x[n/2+o] if i == n/2 - 1 and j == 0 else zero,
        lambda i, k, j: w[i+o][k+o][j+o],
        lambda i, j: A2(i, j, n, o),
        lambda i, j: A2(i+n/2, j+n/2, n, o))

for i in range(n):
  for j in range(i+1, n):
    assert A1(i, j, n, 0) == A2(i, j, n, 0)

print "OK"

