import z3


def solve(grid):
    """

    . . .
    .1.1.
    . .3.

    """
    s = z3.Solver()

    # Construct atoms to represent the dots
    Dot = z3.Datatype("Dot")
    for d in grid.dots():
        Dot.declare("dot_{}".format(d))
    Dot = Dot.create()

    dot_atom = {d: getattr(Dot, "dot_{}".format(d))
                for d in grid.dots()
                }

    # Booleans for each of the points
    dot = {d: z3.Bool("dot-{}".format(d)) for d in grid.dots()}

    # Booleans for each of the connectors
    line = {l: z3.Bool("line-{}".format(l))
            for l in grid.lines()}

    # For each point: if it is on, it must have precisely two adjoining lines activated
    # If it's off, then there are zero adjoining lines activated
    bool_to_int = z3.Function("bool_to_int", z3.BoolSort(), z3.IntSort())
    s.add(bool_to_int(True) == 1)
    s.add(bool_to_int(True) != 0)
    s.add(bool_to_int(False) == 0)
    s.add(bool_to_int(False) != 1)

    for d in grid.dots():
        # Get all lines coming out of this dot
        ls = [line[l] for l in d.lines()]

        sm = z3.Sum(*(bool_to_int(l) for l in ls))
        s.add(z3.Implies(dot[d], sm == 2))
        s.add(z3.Implies(z3.Not(dot[d]), sm == 0))

    # For each line: if it is activated, then the points at both ends are activated
    for l in line:
        d1, d2 = l.ends()
        s.add(z3.Implies(line[l], z3.And(dot[d1], dot[d2])))

    # "Is connected to" relationship
    connected = z3.Function("connected", Dot, Dot, z3.BoolSort())

    # For each line:
    # The Dot at each end is connected to the other iff the line is activated
    for d1 in grid.dots():
        for d2 in grid.dots():
            a = dot_atom[d1]
            b = dot_atom[d2]
            if (l := grid.line(d1, d2)) is None:
                # These dots are never connected
                s.add(connected(a, b) != True)
            else:
                s.add(z3.Implies(line[l], connected(a, b)))
                s.add(z3.Implies(z3.Not(line[l]), z3.Not(connected(a, b))))

    # Transitive closure of "is connected to"
    path_connected = z3.TransitiveClosure(connected)

    # For every point, if it's activated then it's transitively connected to a point adjacent to a 3-cell
    xy3 = [xy for (xy, c) in grid.cells() if c == "3"][0]
    dot3 = grid.cell_dots(*xy3)[0]
    atom3 = dot_atom[dot3]

    for d in grid.dots():
        s.add(z3.Implies(dot[d], path_connected(dot_atom[d], atom3)))
        s.add(z3.Implies(z3.Not(dot[d]), z3.Not(path_connected(dot_atom[d], atom3))))

    # Constrain the number of activated lines surrounding each known cell
    def line_count_of_cell(xy):
        """xy is the dot at the top-left
        Return an invocation of line_count for the lines around it.
        """
        return z3.Sum(*(bool_to_int(line[l]) for l in grid.cell_lines(*xy)))

    for xy, c in grid.cells():
        if c != " ":
            print("adding constraint for ", xy, c, [str(l) for l in grid.cell_lines(*xy)])
            s.add(line_count_of_cell(xy) == int(c))

    # Look for a solution.
    print("check: ", s.check())
    # print(s)
    m = s.model()
    # print(m)

    print()
    grid.print(dot_on=lambda d: m.eval(dot[d]),
               line_on=lambda l: m.eval(line[l]))
