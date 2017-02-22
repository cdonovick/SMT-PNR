"""
Convert graphviz to dict for use with smtpnr.build_graph

Requires pygraphviz
"""

import pygraphviz as pg

def from_file(file_name):
    return from_graph(pg.AGraph(file_name))

def from_graph(G):
    assert G.is_directed(), "Graph must be directed"
    adj_dict = dict()
    for node in G:
        adj_dict[node] = []
        for edge in G.out_edges(node):
            adj_dict[node].append((edge[1],1))
    return adj_dict
