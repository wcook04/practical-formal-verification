"""Interchangeable searches for the compatibility verdict. None is proved.

Each search takes two integer transition tables and returns a verdict with
one label per pair of states. `formal/compatibility/Verdict.dfy` decides
whether the verdict may be reported. Three searches are honest and work in
different ways. Three are wrong on purpose.

A table is (next, output, initial). `next[s][a] == -1` means state `s` does
not allow input `a`. A verdict is None for compatible, or the input word on
which the candidate differs. Label -1 claims that no word from that pair
reaches a difference; label n claims that no word shorter than n does.
"""

from collections import deque

NEVER = -1


class Pair:
    """Both tables, read as one graph over pairs of states."""

    def __init__(self, approved, candidate, inputs):
        self.old_next, self.old_output, self.old_initial = approved
        self.new_next, self.new_output, self.new_initial = candidate
        self.inputs = inputs
        self.start = (self.old_initial, self.new_initial)
        self.pairs = [(s, t) for s in range(len(self.old_next))
                      for t in range(len(self.new_next))]

    def allowed(self, pair):
        return [a for a in range(self.inputs) if self.old_next[pair[0]][a] >= 0]

    def differs(self, pair, a):
        s, t = pair
        return (self.new_next[t][a] < 0
                or self.old_output[s][a] != self.new_output[t][a])

    def step(self, pair, a):
        return self.old_next[pair[0]][a], self.new_next[pair[1]][a]

    def table(self, labels, default):
        return [[labels.get((s, t), default) for t in range(len(self.new_next))]
                for s in range(len(self.old_next))]

    def reachable(self):
        seen, queue = {self.start}, deque([self.start])
        while queue:
            pair = queue.popleft()
            for a in self.allowed(pair):
                if not self.differs(pair, a) and self.step(pair, a) not in seen:
                    seen.add(self.step(pair, a))
                    queue.append(self.step(pair, a))
        return seen


def _distances(g):
    """Exact number of inputs to the nearest difference, working backwards."""
    distance, before = {}, {pair: [] for pair in g.pairs}
    for pair in g.pairs:
        for a in g.allowed(pair):
            if g.differs(pair, a):
                distance[pair] = 1
            else:
                before[g.step(pair, a)].append(pair)
    queue = deque(distance)
    while queue:
        pair = queue.popleft()
        for earlier in before[pair]:
            if earlier not in distance:
                distance[earlier] = distance[pair] + 1
                queue.append(earlier)
    return distance


def _walk(g, distance, order):
    pair, word = g.start, []
    while True:
        remaining = distance[pair] - 1
        for a in order(g.allowed(pair)):
            if g.differs(pair, a) if remaining == 0 else (
                    not g.differs(pair, a)
                    and distance.get(g.step(pair, a)) == remaining):
                word.append(a)
                break
        if remaining == 0:
            return word
        pair = g.step(pair, word[-1])


def backward(approved, candidate, inputs):
    """Measure every pair's distance to a difference, then walk downhill."""
    g = Pair(approved, candidate, inputs)
    distance = _distances(g)
    labels = g.table(distance, NEVER)
    if g.start not in distance:
        return None, labels
    return _walk(g, distance, sorted), labels


def forward(approved, candidate, inputs):
    """Breadth-first from the start for the word; labels by repeated relaxing."""
    g = Pair(approved, candidate, inputs)
    parents, queue, word = {g.start: None}, deque([g.start]), None
    while queue and word is None:
        pair = queue.popleft()
        for a in g.allowed(pair):
            if g.differs(pair, a):
                word = [a]
                while parents[pair] is not None:
                    pair, previous = parents[pair]
                    word.append(previous)
                word.reverse()
                break
            if g.step(pair, a) not in parents:
                parents[g.step(pair, a)] = (pair, a)
                queue.append(g.step(pair, a))
    unknown = len(g.pairs) + 1
    labels, changed = {pair: unknown for pair in g.pairs}, True
    while changed:
        changed = False
        for pair in g.pairs:
            best = min([1 if g.differs(pair, a) else 1 + labels[g.step(pair, a)]
                        for a in g.allowed(pair)], default=unknown)
            if best < labels[pair]:
                labels[pair], changed = best, True
    labels = {pair: NEVER if n >= unknown else n for pair, n in labels.items()}
    return word, g.table(labels, NEVER)


def deepening(approved, candidate, inputs):
    """Depth-first with a growing limit. Labels are only what it ruled out."""
    g = Pair(approved, candidate, inputs)
    ruled_out = {}

    def within(pair, limit):
        if ruled_out.setdefault(pair, 0) >= limit:
            return None
        for a in g.allowed(pair):
            if g.differs(pair, a):
                return [a]
            rest = within(g.step(pair, a), limit - 1)
            if rest is not None:
                return [a] + rest
        ruled_out[pair] = limit
        return None

    for limit in range(1, len(g.pairs) + 1):
        word = within(g.start, limit)
        if word is not None:
            return word, g.table({p: n + 1 for p, n in ruled_out.items()}, 1)
    return None, g.table({pair: NEVER for pair in g.reachable()}, 1)


def largest_input_first(approved, candidate, inputs):
    """WRONG: a shortest word, but ties go to the largest input."""
    g = Pair(approved, candidate, inputs)
    distance = _distances(g)
    labels = g.table(distance, NEVER)
    if g.start not in distance:
        return None, labels
    return _walk(g, distance, lambda actions: sorted(actions, reverse=True)), labels


def initial_state_only(approved, candidate, inputs):
    """WRONG: looks for a difference in the initial states and nowhere else."""
    g = Pair(approved, candidate, inputs)
    for a in g.allowed(g.start):
        if g.differs(g.start, a):
            return [a], g.table({g.start: 1}, 0)
    return None, g.table({pair: NEVER for pair in g.reachable()}, 0)


def first_found(approved, candidate, inputs):
    """WRONG: reports the first difference a depth-first walk meets."""
    g = Pair(approved, candidate, inputs)
    distance, seen = _distances(g), set()

    def walk(pair):
        seen.add(pair)
        for a in g.allowed(pair):
            if g.differs(pair, a):
                return [a]
            if g.step(pair, a) not in seen:
                rest = walk(g.step(pair, a))
                if rest is not None:
                    return [a] + rest
        return None

    word = walk(g.start)
    if word is None:
        return None, g.table(distance, NEVER)
    return word, g.table({**distance, g.start: len(word)}, NEVER)


HONEST = (backward, forward, deepening)
WRONG = (largest_input_first, initial_state_only, first_found)
