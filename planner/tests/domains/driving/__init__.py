import os, sys
from math import tanh

from map import Map

def sig(value):
    return tanh(value)

def isig(value):
    return 1-tanh(value)

def sigm(value):
    return (tanh(value)+1)/2.
    
def isigm(value):
    return 1-sigm(value)

basePath = os.path.dirname(os.path.abspath(__file__))
map = Map.load(os.path.join(basePath, 'points.csv'), os.path.join(basePath, 'connections.csv'))

dist = map.dist

iter_neighbors = map.iter_neighbors
