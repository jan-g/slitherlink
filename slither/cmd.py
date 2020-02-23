import collections
import itertools
import z3


class Grid:
    def __init__(self, *grid):
        self.grid = grid
        self.max_x = len(grid[0])
        self.max_y = len(grid)

    class Dot:
        def __init__(self, grid, *coord):
            self.grid = grid
            self.coord = coord

        def __str__(self):
            return "-".join(str(x) for x in self.coord)

        def __eq__(self, other):
            return isinstance(other, Grid.Dot) and self.coord == other.coord

        def __hash__(self):
            return hash(self.coord)

        def lines(self):
            x, y = self.coord
            lines = []
            for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                c2 = (x + dx, y + dy)
                if (l := self.grid.line(self.coord, c2)) is not None:
                    lines.append(l)
            return lines

    def dots(self):
        return [Grid.Dot(self, x, y) for x in range(self.max_x + 1) for y in range(self.max_y + 1)]

    def dot(self, *coord):
        (x, y) = coord
        if 0 <= x <= self.max_x and 0 <= y <= self.max_y:
            return Grid.Dot(self, x, y)

    class Line:
        def __init__(self, grid, d1, d2):
            self.grid = grid
            self.d1 = d1
            self.d2 = d2

        def ends(self):
            return [self.d1, self.d2]

        def __eq__(self, other):
            return isinstance(other, Grid.Line) and ((other.d1, other.d2) == (self.d1, self.d2))

        def __hash__(self):
            return hash(self.d1) ^ hash(self.d2)

        def __str__(self):
            return "{}-{}".format(self.d1, self.d2)

    def line(self, c1, c2):
        if isinstance(c1, Grid.Dot) and isinstance(c2, Grid.Dot):
            return self.line(c1.coord, c2.coord)
        if c2 < c1:
            c1, c2 = c2, c1
        d1 = self.dot(*c1)
        d2 = self.dot(*c2)
        if d1 is not None and d2 is not None:
            (x1, y1) = c1
            (x2, y2) = c2
            # Check for adjacency
            if abs(y2 - y1) + abs(x2 - x1) == 1:
                return Grid.Line(self, d1, d2)

    def lines(self):
        lines = []
        for d1 in self.dots():
            (x1, y1) = d1.coord
            for dx, dy in (1, 0), (0, 1):
                (x2, y2) = (x1 + dx, y1 + dy)
                d2 = self.dot(x2, y2)
                if d2 is not None:
                    lines.append(Grid.Line(self, d1, d2))
        return lines

    def cell(self, *coord):
        (x, y) = coord
        return self.grid[y][x]

    def cells(self):
        return [((x, y), self.cell(x, y)) for x in range(self.max_x) for y in range(self.max_y)]

    def cell_dots(self, *coord):
        x, y = coord
        return [self.dot(x + dx, y + dy) for dx in (0, 1) for dy in (0, 1)]

    def cell_lines(self, *coord):
        x, y = coord
        return [self.line((x, y), (x + 1, y)),
                self.line((x, y), (x, y + 1)),
                self.line((x, y + 1), (x + 1, y + 1)),
                self.line((x + 1, y), (x + 1, y + 1)),
                ]

def main(grid):
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
            s.add(line_count_of_cell(xy) == int(c))

    # Look for a solution.
    print("check: ", s.check())
    # print(s)
    m = s.model()
    # print(m)

    print()
    for row in range(grid.max_y + 1):
        if row > 0:
            for col in range(grid.max_x + 1):
                if col > 0:
                    print(grid.cell(col - 1, row - 1), end="")
                print("|" if m.eval(line[grid.line((col, row - 1), (col, row))]) else " ", end="")
            print()
        for col in range(grid.max_x + 1):
            if col > 0:
                print("-" if m.eval(line[grid.line((col - 1, row), (col, row))]) else " ", end="")
            print("*" if m.eval(dot[grid.dot(col, row)]) else ".", end="")
        print()


if __name__ == '__main__':
    main(Grid("11", " 3"))
    print()
    main(Grid(" 20 33 ",
              "1  1  1",
              " 30 13 ",
              "   3   ",
              " 23 21 ",
              "3  1  3",
              " 21 23 "))

    main(Grid("213     33",
              "1    02  2",
              "   0 2 1  ",
              "  21 313  ",
              "03       1",
              "2       20",
              "  011 20  ",
              "  3 3 3   ",
              "2  11    3",
              "22     101"))
