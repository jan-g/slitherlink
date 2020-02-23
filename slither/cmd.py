import collections
import itertools
import z3


def main(*grid):
    """

    . . .
    .1.1.
    . .3.

    """
    max_x = len(grid[0])
    max_y = len(grid)
    XS = list(range(max_x + 1))
    YS = list(range(max_y + 1))

    s = z3.Solver()

    # Construct atoms to represent the dots
    Dot = z3.Datatype("Dot")
    for (x, y) in ((x, y) for x in XS for y in YS):
        Dot.declare("dot_{}_{}".format(x, y))
    Dot = Dot.create()

    dot_atoms = {(x, y): getattr(Dot, "dot_{}_{}".format(x, y))
                 for (x, y) in ((x, y) for x in XS for y in YS)
                 }

    def dot_atom(x, y):
        return dot_atoms[(x, y)]

    # Booleans for each of the points
    dots = [[z3.Bool("dot-{}-{}".format(x, y)) for x in XS] for y in YS]

    def dot(x, y):
        return dots[y][x]

    # Booleans for each of the connectors
    lines = collections.defaultdict(dict)
    for x1, y1 in itertools.product(XS, YS):
        for dx, dy in ((1, 0), (0, 1)):
            x2, y2 = x1 + dx, y1 + dy
            if 0 <= x2 <= max_x and 0 <= y2 <= max_y:
                lines[x1, y1][x2, y2] = z3.Bool("line-{}-{}-{}-{}".format(x1, y1, x2, y2))

    def line(c1, c2):
        if c1 in lines and c2 in lines[c1]:
            return lines[c1][c2]
        elif c2 in lines and c1 in lines[c2]:
            return lines[c2][c1]
        else:
            return None

    # For each point: if it is on, it must have precisely two adjoining lines activated
    # If it's off, then there are zero adjoining lines activated
    bool_to_int = z3.Function("bool_to_int", z3.BoolSort(), z3.IntSort())
    s.add(bool_to_int(True) == 1)
    s.add(bool_to_int(True) != 0)
    s.add(bool_to_int(False) == 0)
    s.add(bool_to_int(False) != 1)

    for x, y in itertools.product(XS, YS):
        # Get all lines coming out of this dot
        ls = [l
              for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1))
              if (l := line((x, y), (x+dx, y+dy))) is not None]

        sm = z3.Sum(*(bool_to_int(l) for l in ls))
        s.add(z3.Implies(dot(x, y), sm == 2))
        s.add(z3.Implies(z3.Not(dot(x, y)), sm == 0))

    # For each line: if it is activated, then the points at both ends are activated
    for x, y in itertools.product(XS, YS):
        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            x2 = x + dx
            y2 = y + dy
            if (l := line((x, y), (x2, y2))) is None:
                continue
            s.add(z3.Implies(l, z3.And(dot(x, y), dot(x2, y2))))

    # "Is connected to" relationship
    connected = z3.Function("connected", Dot, Dot, z3.BoolSort())

    # For each line:
    # The Dot at each end is connected to the other iff the line is activated
    for x, y in itertools.product(XS, YS):
        for x2, y2 in itertools.product(XS, YS):
            a = dot_atom(x, y)
            b = dot_atom(x2, y2)
            if (l := line((x, y), (x2, y2))) is None:
                # These dots are never connected
                s.add(connected(a, b) != True)
            else:
                s.add(z3.Implies(l, connected(a, b)))
                s.add(z3.Implies(z3.Not(l), z3.Not(connected(a, b))))

    # Transitive closure of "is connected to"
    path_connected = z3.TransitiveClosure(connected)

    # For every point, if it's activated then it's transitively connected to a point adjacent to a 3-cell
    x3, y3 = [(x, y) for (x, y) in itertools.product(range(max_x), range(max_y)) if grid[y][x] == "3"][0]

    for x, y in itertools.product(XS, YS):
        s.add(z3.Implies(dot(x, y), path_connected(dot_atom(x, y), dot_atom(x3, y3))))
        s.add(z3.Implies(z3.Not(dot(x, y)), z3.Not(path_connected(dot_atom(x, y), dot_atom(x3, y3)))))

    # Constrain the number of activated lines surrounding each known cell
    def line_count_of_cell(x, y):
        """(x, y) is the dot at the top-left
        Return an invocation of line_count for the lines around it.
        """
        lt = line((x, y), (x + 1, y))
        lb = line((x, y + 1), (x + 1, y + 1))
        ll = line((x, y), (x, y + 1))
        lr = line((x + 1, y), (x + 1, y + 1))
        return bool_to_int(lt) + bool_to_int(lb) + bool_to_int(ll) + bool_to_int(lr)

    for (y, ln) in enumerate(grid):
        for (x, c) in enumerate(ln):
            if c != " ":
                s.add(line_count_of_cell(x, y) == int(c))

    # Look for a solution.
    print("check: ", s.check())
    # print(s)
    m = s.model()
    # print(m)

    print()
    for row in YS:
        if row > 0:
            for col in XS:
                if col > 0:
                    print(grid[row - 1][col - 1], end="")
                print("|" if m.eval(line((col, row - 1), (col, row))) else " ", end="")
            print()
        for col in XS:
            if col > 0:
                print("-" if m.eval(line((col - 1, row), (col, row))) else " ", end="")
            print("*" if m.eval(dot(col, row)) else ".", end="")
        print()


if __name__ == '__main__':
    main("11", " 3")
    print()
    main(" 20 33 ",
         "1  1  1",
         " 30 13 ",
         "   3   ",
         " 23 21 ",
         "3  1  3",
         " 21 23 ")

    main("213     33",
         "1    02  2",
         "   0 2 1  ",
         "  21 313  ",
         "03       1",
         "2       20",
         "  011 20  ",
         "  3 3 3   ",
         "2  11    3",
         "22     101")
