from slither.solve import solve


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

    def print(self, dot_on, line_on):
        for row in range(self.max_y + 1):
            if row > 0:
                for col in range(self.max_x + 1):
                    if col > 0:
                        print(self.cell(col - 1, row - 1), end="")
                    print("|" if line_on(self.line((col, row - 1), (col, row))) else " ", end="")
                print()
            for col in range(self.max_x + 1):
                if col > 0:
                    print("-" if line_on(self.line((col - 1, row), (col, row))) else " ", end="")
                print("*" if dot_on(self.dot(col, row)) else ".", end="")
            print()


def main():
    solve(Grid("11", " 3"))
    print()
    solve(Grid(" 20 33 ",
               "1  1  1",
               " 30 13 ",
               "   3   ",
               " 23 21 ",
               "3  1  3",
               " 21 23 "))

    solve(Grid("213     33",
               "1    02  2",
               "   0 2 1  ",
               "  21 313  ",
               "03       1",
               "2       20",
               "  011 20  ",
               "  3 3 3   ",
               "2  11    3",
               "22     101"))


if __name__ == '__main__':
    main()
