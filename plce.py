import re
import rstr
import random
from pyformlang.cfg import CFG, Variable, Terminal
from collections import deque
import string
import sys
sys.modules["rstr.xeger"].STAR_PLUS_LIMIT = 10

def xeger_capped(pattern, min_len, max_len, tries=10000):
  for _ in range(tries):
    s = rstr.xeger(pattern)
    if min_len <= len(s) <= max_len:
      return s
  return None

patterns = {
    # basics
    "any binary string":             r"[01]*",
    "nonempty":                      r"[01]+",
    "starts with 0":                 r"0[01]*",
    "ends with 1":                   r"[01]*1",
    "starts and ends with same":     r"0([01]*0)?|1([01]*1)?",

    # substrings
    "contains 101":                  r"[01]*101[01]*",
    "does not contain 11":           r"(0|10)*1?",
    "every 1 followed by a 0":       r"(0|10)*",
    "all 0s then all 1s":            r"0*1*",
    "alternating 0s and 1s":         r"1?(01)*0?",

    # counting
    "exactly two 1s":                r"0*10*10*",
    "at least two 1s":               r"[01]*1[01]*1[01]*",
    "at most one 1":                 r"0*1?0*",
    "even number of 0s":             r"1*(01*01*)*",
    "even number of 1s":             r"0*(10*10*)*",

    # length / position
    "even length":                   r"([01]{2})*",
    "length divisible by 3":         r"([01]{3})*",
    "third symbol from end is 1":    r"[01]*1[01]{2}",

    # arithmetic
    "binary number divisible by 3":  r"(0|1(01*0)*1)*",
    "test1" : r"((ab|ba)*c(a|bb)*d?|(aab|bba)+c*)((abc|bca)?(a|bb|aba)*d)+"
}

grammars = {
  "n 0's followed by n 1's" : CFG.from_text("""S -> 0 S 1
                                               S -> $"""),
  "arithmetic" : CFG.from_text("""S -> 0
                                  S -> 1
                                  S -> S Op S
                                  S -> ( S )
                                  Op -> +
                                  Op -> -
                                  Op -> *
                                  Op -> /"""),
 "palindromes"   :  CFG.from_text("""S -> $
                                  S -> a
                                  S -> b
                                  S -> a S a
                                  S -> b S b"""),
 "balanced parentheses"   :  CFG.from_text("""S -> $
                                              S -> ( S )
                                              S -> S S"""),
  "English Grammar"  : CFG.from_text(""" S -> NP VP
                                         NP -> CN
                                         NP -> CN PP
                                         VP -> CV
                                         VP -> CV PP
                                         PP -> P CN
                                         CN -> A N
                                         CV -> V
                                         CV -> V NP
                                         A -> a
                                         N -> n
                                         V -> v
                                         P -> p

""")
}

def test(re_or_cfg, i_re_or_cfg, s):
    if (not i_re_or_cfg):
        return re.fullmatch(re_or_cfg, s) is not None
    else:
      return re_or_cfg.contains(s)

def pumping_splits(s, p):
  for xy_len in range(1, p + 1):
    for x_len in range(xy_len):
      yield [s[:x_len], s[x_len:xy_len], s[xy_len:]]

# given x, y, z, return a list of xy^iz for all i up to n

def pump_string(x, y, z, n):
  pumps = []
  for i in range(n):
    pumps.append(x + y*i + z)
  return pumps


def cfg_to_dict(grammar):
  terminals = {t.value for t in grammar.terminals}
  for t in terminals:
    if len(t) != 1:
      raise ValueError(f"terminal {t!r} is longer than one character")

  # Pick unused single characters for the variables: A-Z first, then others.
  candidates = (c for c in string.ascii_uppercase + "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ"
                if c not in terminals)
  names = {}
  # Keep a variable's own name when it is already a free single character.
  for v in grammar.variables:
    if len(v.value) == 1 and v.value not in terminals:
      names[v] = v.value
  used = set(names.values())
  for v in grammar.variables:
    if v not in names:
      c = next(c for c in candidates if c not in used)
      names[v] = c
      used.add(c)

  rules = {names[v]: [] for v in grammar.variables}
  for prod in grammar.productions:
    rhs = ""
    for sym in prod.body:
      if isinstance(sym, Variable):
        rhs += names[sym]
      elif isinstance(sym, Terminal) and sym.value != "$":
        rhs += sym.value
      # Epsilon contributes nothing
    rules[names[prod.head]].append(rhs)
  return rules, names[grammar.start_symbol]


def random_derive(rules, start="S", max_len=20):
  s = start
  while any(c in rules for c in s):
    if len(s) > max_len * 2:          # string is running away, give up
      return None
    i = next(i for i, c in enumerate(s) if c in rules)   # leftmost variable
    s = s[:i] + random.choice(rules[s[i]]) + s[i+1:]
  return s


def random_string_simple(rules, min_len, max_len, start="S", tries=10000):
  for _ in range(tries):
    s = random_derive(rules, start=start, max_len=max_len)
    if s is not None and min_len <= len(s) <= max_len:
      return s
  return None


def apply_lemma(re_or_cfg, i_re_or_cfg, str, p, num_divisons, num_pumps):
  if len(str) < p:
    print("To apply the pumping lemma str must be at least p characters long")
    return

  division_gen = pumping_splits(str, p)
  max_split = (p*(p+1))//2
  for i in range(min(num_divisons, max_split)):

    division = next(division_gen)

    pumps = pump_string(division[0], division[1], division[2], num_pumps)


    passes = True
    for pump in pumps:
      if (not test(re_or_cfg, i_re_or_cfg, pump)):
        passes = False
        break

    if passes:
      print("division", division, " passes")
      return True
    else:
      print("division", division, " does not pass")
      pass
  return False


def enumerate_simple(rules, min_len, max_len, start="S"):
  seen, queue, results = set(), deque([start]), set()
  while queue:
    s = queue.popleft()
    if sum(c not in rules for c in s) > max_len:   # too many terminals already
      continue
    if not any(c in rules for c in s):             # no variables left: a real string
      if len(s) >= min_len:
        results.add(s)
      continue
    i = next(i for i, c in enumerate(s) if c in rules)
    for rhs in rules[s[i]]:
      t = s[:i] + rhs + s[i+1:]
      if t not in seen and len(t) <= max_len * 2 + 1:
        seen.add(t)
        queue.append(t)
  return sorted(results, key=lambda x: (len(x), x))


def enumerate_by_length(rules, min_len, max_len, start="S"):
  for n in range(min_len, max_len + 1):
    for s in enumerate_simple(rules, n, n, start=start):
      yield s

p_running = True
while(p_running):
  passed_strings = 0
  failed_strings = 0
  failed_strings_lst = []

  pumping_length = input('Enter Pumping Length: ')
  pumping_length = int(pumping_length)

  # display each key in patterns
  print()
  print('Patterns and Grammars:')
  print()

  for pattern in patterns:
      print(pattern)
  for grammar in grammars:
    print(grammar)

  print()

  pattern_str = input("Enter pattern or grammar to test: ")
  pattern_or_grammar = 0

  if pattern_str in patterns:
    pattern = patterns[pattern_str]
    pattern_or_grammar = 0
  elif pattern_str in grammars:
    pattern = grammars[pattern_str]
    pattern_or_grammar = 1
    rules, start_symbol = cfg_to_dict(pattern)
  else:
    print("Pattern or grammar not found")
    continue

  sampling_mode = "random"
  if pattern_or_grammar:
    mode = input("Sampling mode - (r)andom or (e)numerate: ").strip().lower()
    if mode.startswith("e"):
      sampling_mode = "enumerate"

  num_str_to_test = input("Enter number of strings to test: ")
  num_str_to_test = int(num_str_to_test)

  print("Enter number of divisions (Maximum divisions for p is ", pumping_length*(pumping_length+1)//2, "): ", end="")
  num_divisons = input()
  num_divisons = int(num_divisons)

  num_pumps = input("Enter number of pumps: ")
  num_pumps = int(num_pumps)
  print()

  # enumerate mode walks the language shortest-first, starting at length p
  if pattern_or_grammar and sampling_mode == "enumerate":
    string_source = enumerate_by_length(rules, pumping_length, pumping_length + 10, start=start_symbol)

  for i in range(num_str_to_test):
    if not pattern_or_grammar:
      sys.modules["rstr.xeger"].STAR_PLUS_LIMIT = pumping_length + 10
      test_string = xeger_capped(pattern, pumping_length, pumping_length + 10)
    elif sampling_mode == "enumerate":
      test_string = next(string_source, None)
    else:
      test_string = random_string_simple(rules, pumping_length, pumping_length + 10, start=start_symbol)

    if test_string is None:
      print("No more strings found with length between", pumping_length, "and", pumping_length + 10)
      break

    print("test string", test_string)
    if(apply_lemma(pattern, pattern_or_grammar, test_string, pumping_length, num_divisons, num_pumps)) :
      print("The test string has a decomposition.")
      passed_strings += 1
    else:
      print(f"The string {test_string} cannot pass the pumping lemma with p = {pumping_length}.")
      failed_strings += 1
      failed_strings_lst.append(test_string)
      con_search = input("Continue searching for more counterexamples? (Y/N) ")
      if con_search == "N":
        break
    print()

  print("Strings tested: ", passed_strings + failed_strings)
  print("Strings passed: ", passed_strings)
  print("Strings failed: ", failed_strings)
  print("Counterexamples:", failed_strings_lst)
  p_running = False if input("Continue? ") == "No" else True