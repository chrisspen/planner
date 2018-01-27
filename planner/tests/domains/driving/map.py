import os
import csv
import unittest
from collections import defaultdict
from math import sqrt

#http://networkx.lanl.gov/reference/generated/networkx.DiGraph.add_edge.html
import networkx as nx
import matplotlib

matplotlib.use('Agg')

inf = 1e99999999

class Map(object):

    def __init__(self):
        self.points = {} # {name:(x,y)}
        self.connections = defaultdict(lambda: defaultdict(int)) # {from:{to:time}}

    def add_point(self, name, x, y):
        self.points[name] = (x, y)

    def add_connection(self, from_point, to_point, time):
        assert from_point in self.points
        assert to_point in self.points
        self.connections[from_point][to_point] = time

    def dist(self, from_point, to_point):
        """
        Calculate Euclidean distance between two points.
        """
        assert from_point in self.points
        assert to_point in self.points
        x0, y0 = self.points.get(from_point, (inf, inf))
        x1, y1 = self.points.get(to_point, (inf, inf))
        return sqrt((y1-y0)**2 + (x1-x0)**2)

    def iter_neighbors(self, from_point):
        """
        Returns a list of (to_point, travel_time) for each neighboring point.
        """
        return self.connections[from_point].iteritems()

    @classmethod
    def load(cls, points_fn, connections_fn):
        """
        Loads a map from point and connection CSV files.
        """
        if not os.path.isfile(points_fn):
            _points_fn = os.path.join(os.path.dirname(os.path.realpath(__file__)), points_fn)
            if os.path.isfile(_points_fn):
                points_fn = _points_fn
        assert os.path.isfile(points_fn), 'Points file does not exist: %s' % points_fn

        if not os.path.isfile(connections_fn):
            _connections_fn = os.path.join(os.path.dirname(os.path.realpath(__file__)), connections_fn)
            if os.path.isfile(_connections_fn):
                connections_fn = _connections_fn
        assert os.path.isfile(connections_fn), 'Connections file does not exist: %s' % connections_fn

        m = cls()
        for row in csv.DictReader(open(points_fn)):
            name = row['name']
            x = int(row['x'])
            y = int(row['y'])
            m.add_point(name, x, y)
        for row in csv.DictReader(open(connections_fn)):
            from_point = row['from']
            to_point = row['to']
            time = int(row['time'])
            m.add_connection(from_point, to_point, time)
        return m

class Test(unittest.TestCase):

    def test_map(self):
        m = Map.load('points.csv', 'connections.csv')
        self.assertEqual(len(m.points), 16)
        cons = [(f, t) for f in m.connections.iterkeys() for t in m.connections[f].iterkeys()]
        self.assertEqual(len(cons), 20)
        self.assertEqual(m.dist('a', 'b'), 2)
        self.assertEqual(
            sorted(m.iter_neighbors('d')),
            [('e', 12), ('f', 5), ('g', 10)],
        )

        g = nx.Graph()
        for point_name in m.points:
            g.add_node(point_name)
        for from_name, other in m.connections.iteritems():
            for to_name, time in other.iteritems():
                g.add_edge(from_name, to_name, length=time)
        #pos = nx.shell_layout(g)#bad
        #pos = nx.random_layout(g)#bad
        #pos = nx.spectral_layout(g)#real bad
        pos = nx.spring_layout(g)
        nx.draw(g, pos)
        import matplotlib.pyplot as plt
        plt.show()

if __name__ == '__main__':
    unittest.main()
