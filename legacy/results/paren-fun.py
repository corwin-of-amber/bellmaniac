class memoize(dict):
  def __init__(self, func):
    self.func = func
  def __call__(self, *args):
    return self[args]
  def __missing__(self, key):
    result = self[key] = self.func(*key)
    return result
plus = min
zero = 10000000000000000000000000000
import random
import sys
sys.setrecursionlimit(2 ** 16)

n = 16
@memoize
def x(v1):
  return random.randint(0, 1000)
@memoize
def w(v1, v2, v3):
  return random.randint(0, 1000)
def c(i, j):
  assert ((((0 <= i) and (i < n)) and (i < j)) and (j < n))
  if (i == (j - 1)):
    return x(i)
  else:
    return reduce(plus, [((c(i, k) + c(k, j)) + w(i, k, j)) for k in xrange((i + 1), j)], zero)
def d1(i, j, n, w, r, s, t, w_0, w_1, w_2, r_0, r_1, s_0, s_1, t_0, t_1):
  assert ((((0 <= i) and (i < n/2)) and (0 <= j)) and (j < n/2))
  if (n < 4):
    return d(i, j, n, w, r, s, t, w_0, w_1, w_2, r_0, r_1, s_0, s_1, t_0, t_1)
  elif ((i < n/4) and (j < n/4)):
    return d1(i, j, n/2, w, (lambda i183, j184: d1(i183, j184, n/2, w, r, s, t, w_0, (n/4 + w_1), w_2, r_0, r_1, s_0, (n/4 + s_1), (n/4 + t_0), t_1)), s, t, w_0, w_1, w_2, 0, 0, s_0, s_1, t_0, t_1)
  elif ((i < n/4) and (not (j < n/4))):
    return d1(i, (j - n/4), n/2, w, (lambda i226, j227: d1(i226, j227, n/2, w, r, s, t, w_0, w_1, (n/4 + w_2), r_0, (n/4 + r_1), s_0, s_1, t_0, (n/4 + t_1))), s, t, w_0, (n/4 + w_1), (n/4 + w_2), 0, 0, s_0, (n/4 + s_1), (n/4 + t_0), (n/4 + t_1))
  elif ((not (i < n/4)) and (j < n/4)):
    return d1((i - n/4), j, n/2, w, (lambda i201, j202: d1(i201, j202, n/2, w, r, s, t, (n/4 + w_0), w_1, w_2, (n/4 + r_0), r_1, (n/4 + s_0), s_1, t_0, t_1)), s, t, (n/4 + w_0), (n/4 + w_1), w_2, 0, 0, (n/4 + s_0), (n/4 + s_1), (n/4 + t_0), t_1)
  elif ((not (i < n/4)) and (not (j < n/4))):
    return d1((i - n/4), (j - n/4), n/2, w, (lambda i253, j254: d1(i253, j254, n/2, w, r, s, t, (n/4 + w_0), w_1, (n/4 + w_2), (n/4 + r_0), (n/4 + r_1), (n/4 + s_0), s_1, t_0, (n/4 + t_1))), s, t, (n/4 + w_0), (n/4 + w_1), (n/4 + w_2), 0, 0, (n/4 + s_0), (n/4 + s_1), (n/4 + t_0), (n/4 + t_1))
  else:
    return None
def b1(i, j, n, w, r, s, t, w1, w_0, w_1, w_2, r_0, r_1, s_0, s_1, t_0, t_1, w1_0, w1_1, w1_2):
  assert (((((0 <= i) and (i < n)) and (i < j)) and (j < n)) and ((i < n/2) and (not (j < n/2))))
  if (n < 4):
    return b0(i, j, n, w, r, s, t, w1, w_0, w_1, w_2, r_0, r_1, s_0, s_1, t_0, t_1, w1_0, w1_1, w1_2)
  elif ((i < n/4) and (j < (n/2 + n/4))):
    return b1(i, (j - n/4), n/2, w, (lambda i93, j94: d1(i93, j94, n/2, w1, r, s, (lambda _v91, _v92: b1(_v91, _v92, n/2, w, r, s, t, w1, (n/4 + w_0), (n/4 + w_1), (n/4 + w_2), (n/4 + r_0), (n/4 + r_1), (n/4 + s_0), (n/4 + s_1), (n/4 + t_0), (n/4 + t_1), (n/4 + w1_0), (n/4 + w1_1), (n/4 + w1_2))), w1_0, (n/4 + w1_1), (n/2 + w1_2), r_0, (n/2 + r_1), s_0, (n/4 + s_1), 0, n/4)), s, t, w1, w_0, (n/4 + w_1), (n/4 + w_2), 0, (-1)*n/4, s_0, s_1, (n/4 + t_0), (n/4 + t_1), w1_0, w1_1, (n/4 + w1_2))
  elif ((i < n/4) and (not (j < (n/2 + n/4)))):
    return b1(i, (j - n/2), n/2, w, (lambda i164, j165: d1(i164, j165, n/2, w1, (lambda i158, j159: d1(i158, j159, n/2, w, r, (lambda _v154, _v155: b1(_v154, _v155, n/2, w, (lambda i93, j94: d1(i93, j94, n/2, w1, r, s, (lambda _v91, _v92: b1(_v91, _v92, n/2, w, r, s, t, w1, (n/4 + w_0), (n/4 + w_1), (n/4 + w_2), (n/4 + r_0), (n/4 + r_1), (n/4 + s_0), (n/4 + s_1), (n/4 + t_0), (n/4 + t_1), (n/4 + w1_0), (n/4 + w1_1), (n/4 + w1_2))), w1_0, (n/4 + w1_1), (n/2 + w1_2), r_0, (n/2 + r_1), s_0, (n/4 + s_1), 0, n/4)), s, t, w1, w_0, (n/4 + w_1), (n/4 + w_2), 0, (-1)*n/4, s_0, s_1, (n/4 + t_0), (n/4 + t_1), w1_0, w1_1, (n/4 + w1_2))), t, w_0, (n/2 + w_1), (3*n/4 + w_2), r_0, (3*n/4 + r_1), 0, n/4, (n/2 + t_0), (3*n/4 + t_1))), s, (lambda _v162, _v163: b1(_v162, _v163, n/2, w, (lambda i124, j125: d1(i124, j125, n/2, w, r, (lambda _v120, _v121: b1(_v120, _v121, n/2, w, r, s, t, w1, (n/4 + w_0), (n/4 + w_1), (n/4 + w_2), (n/4 + r_0), (n/4 + r_1), (n/4 + s_0), (n/4 + s_1), (n/4 + t_0), (n/4 + t_1), (n/4 + w1_0), (n/4 + w1_1), (n/4 + w1_2))), t, (n/4 + w_0), (n/2 + w_1), (3*n/4 + w_2), (n/4 + r_0), (3*n/4 + r_1), 0, n/4, (n/2 + t_0), (3*n/4 + t_1))), s, t, w1, (n/4 + w_0), (n/2 + w_1), (n/2 + w_2), 0, (-1)*n/4, (n/4 + s_0), (n/4 + s_1), (n/2 + t_0), (n/2 + t_1), (n/4 + w1_0), (n/4 + w1_1), (n/2 + w1_2))), w1_0, (n/4 + w1_1), (3*n/4 + w1_2), 0, 0, s_0, (n/4 + s_1), 0, n/4)), s, t, w1, w_0, (n/2 + w_1), (n/2 + w_2), 0, (-1)*n/4, s_0, s_1, (n/2 + t_0), (n/2 + t_1), w1_0, w1_1, (n/2 + w1_2))
  elif ((not (i < n/4)) and (j < (n/2 + n/4))):
    return b1((i - n/4), (j - n/4), n/2, w, r, s, t, w1, (n/4 + w_0), (n/4 + w_1), (n/4 + w_2), (n/4 + r_0), (n/4 + r_1), (n/4 + s_0), (n/4 + s_1), (n/4 + t_0), (n/4 + t_1), (n/4 + w1_0), (n/4 + w1_1), (n/4 + w1_2))
  elif ((not (i < n/4)) and (not (j < (n/2 + n/4)))):
    return b1((i - n/4), (j - n/2), n/2, w, (lambda i124, j125: d1(i124, j125, n/2, w, r, (lambda _v120, _v121: b1(_v120, _v121, n/2, w, r, s, t, w1, (n/4 + w_0), (n/4 + w_1), (n/4 + w_2), (n/4 + r_0), (n/4 + r_1), (n/4 + s_0), (n/4 + s_1), (n/4 + t_0), (n/4 + t_1), (n/4 + w1_0), (n/4 + w1_1), (n/4 + w1_2))), t, (n/4 + w_0), (n/2 + w_1), (3*n/4 + w_2), (n/4 + r_0), (3*n/4 + r_1), 0, n/4, (n/2 + t_0), (3*n/4 + t_1))), s, t, w1, (n/4 + w_0), (n/2 + w_1), (n/2 + w_2), 0, (-1)*n/4, (n/4 + s_0), (n/4 + s_1), (n/2 + t_0), (n/2 + t_1), (n/4 + w1_0), (n/4 + w1_1), (n/2 + w1_2))
  else:
    return None
def c1(i, j, n, w, r, w_0, w_1, w_2, r_0, r_1):
  assert ((((0 <= i) and (i < n)) and (i < j)) and (j < n))
  if (n < 4):
    return c0(i, j, n, w, r, w_0, w_1, w_2, r_0, r_1)
  elif ((i < n/2) and (j < n/2)):
    return c1(i, j, n/2, w, r, w_0, w_1, w_2, r_0, r_1)
  elif ((i < n/2) and (not (j < n/2))):
    return b1(i, j, n, w, r, (lambda _v27, _v28: c1(_v27, _v28, n/2, w, r, w_0, w_1, w_2, r_0, r_1)), (lambda _v34, _v35: c1(_v34, _v35, n/2, w, r, (n/2 + w_0), (n/2 + w_1), (n/2 + w_2), (n/2 + r_0), (n/2 + r_1))), w, w_0, w_1, w_2, r_0, r_1, 0, 0, (-1)*n/2, (-1)*n/2, w_0, w_1, w_2)
  elif ((not (i < n/2)) and (not (j < n/2))):
    return c1((i - n/2), (j - n/2), n/2, w, r, (n/2 + w_0), (n/2 + w_1), (n/2 + w_2), (n/2 + r_0), (n/2 + r_1))
  else:
    return None
def r(i, j):
  assert ((((0 <= i) and (i < n)) and (i < j)) and (j < n))
  if (i == (j - 1)):
    return x(i)
  else:
    return zero
def c0(i, j, n, w, r, w_0, w_1, w_2, r_0, r_1):
  assert ((((0 <= i) and (i < n)) and (i < j)) and (j < n))
  return plus(reduce(plus, [((c0(i, k, n, w, r, w_0, w_1, w_2, r_0, r_1) + c0(k, j, n, w, r, w_0, w_1, w_2, r_0, r_1)) + w((i + w_0), (k + w_1), (j + w_2))) for k in xrange((i + 1), j)], zero), r((i + r_0), (j + r_1)))
def b0(i, j, n, w, r, s, t, w1, w_0, w_1, w_2, r_0, r_1, s_0, s_1, t_0, t_1, w1_0, w1_1, w1_2):
  assert (((((0 <= i) and (i < n)) and (i < j)) and (j < n)) and ((i < n/2) and (not (j < n/2))))
  return plus(reduce(plus, [((s((i + s_0), (k1 + s_1)) + b0(k1, j, n, w, r, s, t, w1, w_0, w_1, w_2, r_0, r_1, s_0, s_1, t_0, t_1, w1_0, w1_1, w1_2)) + w1((i + w1_0), (k1 + w1_1), (j + w1_2))) for k1 in xrange((i + 1), n/2)] + [((b0(i, k2, n, w, r, s, t, w1, w_0, w_1, w_2, r_0, r_1, s_0, s_1, t_0, t_1, w1_0, w1_1, w1_2) + t((k2 + t_0), (j + t_1))) + w((i + w_0), (k2 + w_1), (j + w_2))) for k2 in xrange(n/2, j)], zero), r((i + r_0), (j + r_1)))
def d(i, j, n, w, r, s, t, w_0, w_1, w_2, r_0, r_1, s_0, s_1, t_0, t_1):
  assert ((((0 <= i) and (i < n/2)) and (0 <= j)) and (j < n/2))
  return plus(reduce(plus, [((s((i + s_0), (k + s_1)) + t((k + t_0), (j + t_1))) + w((i + w_0), (k + w_1), (j + w_2))) for k in xrange(0, n/2)], zero), r((i + r_0), (j + r_1)))
