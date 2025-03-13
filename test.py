def strip(e: dict[str, float]) -> dict[str, float]:
  return {v: c for v, c in e.items() if c != 0}

def plus(e1: dict[str, float], e2: dict[str, float]) -> dict[str, float]:
  e = dict(e1)
  for v, c in e2.items():
    if v in e:
      e[v] += c
    else:
      e[v] = c
  return strip(e)


def plus_all(*es: list[dict[str, float]]) -> dict[str, float]:
  result = {}
  for e in es:
    result = plus(result, e)
  return result


def mult(e: dict[str, float], m: float) -> dict[str, float]:
  return {v: m * c for v, c in e.items()}


def minus(e1: dict[str, float], e2: dict[str, float]) -> dict[str, float]:
  return plus(e1, mult(e2, -1))

a = 'a'
b = 'b'
c = 'b'
d = 'a'

expr = list(minus({a: 1, b: -1}, {c: 1, d: -1}).items())

print(expr)