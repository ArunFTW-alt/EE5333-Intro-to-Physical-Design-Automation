# -*- coding: utf-8 -*-
"""EP22B004.ipynb

Automatically generated by Colab.

Original file is located at
    https://colab.research.google.com/drive/1fIb4fCH143DFyGew0oBzVGyMwRXPxaZ5

### **Random Graph Algorithm Generation Code**

This code is to generate a graph to test hierarchial partitioning algorithm
"""

import networkx as nx
import matplotlib.pyplot as plt
import random

V = 10000
probability = 0.003

# Generate a random graph
G = nx.erdos_renyi_graph(n=V, p=probability, seed=random.seed())

# Draw the graph
'''plt.figure(figsize=(8, 6))
nx.draw(G, with_labels=True, node_color='lightblue', node_size=30, font_weight='bold')
plt.title("Random Graph")
plt.show()'''
E = list(G.edges)
print(len(E))

"""### **Hierarchial Partition**

#### Function to create an initial partition
"""

#Create Initial Partition
Av = [1 for _ in range(V)]
def initial_partition(V, Av):
    skew = max(Av)/sum(Av)
    sorted_vertices = sorted(range(V), key=lambda x: Av[x], reverse=True)
    A, B = [], []
    area_A, area_B = 0, 0
    tot = sum(Av)
    for v in sorted_vertices:
        if area_A <= area_B and area_A + Av[v] <= tot*(0.5 + skew/2):
            A.append(v)
            area_A += Av[v]
        elif area_B + Av[v] <= tot*(0.5 + skew/2):
            B.append(v)
            area_B += Av[v]
        else:
            # If we can't add to B, try adding to A as a last resort
            if area_A + Av[v] <= tot*(0.5+skew/2):
                A.append(v)
                area_A += Av[v]
            else:
                # If we can't add to either, just add to B (this might violate skew temporarily)
                B.append(v)
                area_B += Av[v]
    while area_A < (0.5-skew/2)*tot and B:
        v = B.pop(0)
        A.append(v)
        area_A += Av[v]
        area_B -= Av[v]
    partition = [0 for i in range(V)]
    for i in A:
        partition[i] = 1
    return partition
ipart = initial_partition(V,Av)
print(ipart)

"""#### Function to calculate the Gain table (or Cost table)"""

#Gain Calculator
# This function works for hyperedges as well.
def cost(V,E,part,T):
    g = [None for _ in range(V)]
    for he in E:
        nA = []
        nB = []
        for i in he:
            if part[i]==1:
                nA.append(i)
            else:
                nB.append(i)
        if not (nA and nB):
            for i in he:
                if not g[i]:
                    g[i] = 0
                g[i] -= 1 # Edges lying in the same partition
        else:
            if len(nA)==len(nB) and len(nA)==1:
                for i in he:
                    if not g[i]:
                        g[i] = 0
                    g[i] += 1 #Edges having vertices on different sides.
            else: # Occurs only in unevenly cut hyperedges which is not a part of this assignment.
                if len(nA)>len(nB):
                    for j in nB:
                        if not g[j]:
                            g[j] = 0
                        g[j] += 1
    for i in range(V): #Not accounting for vertices which are fixed(vertices in the list T)
        if not g[i]:
            g[i] = 0
        if i in T:
            g[i] = None
    return g

"""#### Function to calculate the number of cuts"""

def cuts(E,part): #However this works only for simple graphs.
    cuts = 0
    for u,v in E:
        if part[v]^part[u]:
            cuts+=1
    return cuts
print(cuts(E,ipart))

"""#### Function which is responsible for coarsening."""

def coarser(N, E, proportion=0.5): #Proportion as 0.5 is very high for higher order graphs. So it will be adjusted in the final function
    S = [[] for _ in range(N)] #Creating Adjacency list for conveniences.
    for u, v in E:
        S[u].append(v)
        S[v].append(u)

    degrees = {i: len(S[i]) for i in range(N)}
    sorted_vertices = sorted(degrees.items(), key=lambda x: -x[1]) #Sorting the vertices on basis of degrees in descending order
    remaining_vertices = set(range(N))
    supervertices = []
    max_supervertex_size = max(1, int(proportion * N))

    for vertex, degree in sorted_vertices:
        if vertex in remaining_vertices:
            supervertex = [vertex]
            remaining_vertices.remove(vertex)
            neighbors = sorted((v for v in S[vertex] if v in remaining_vertices), key=lambda x: degrees[x], reverse=True)

            for neighbor in neighbors:
                if len(supervertex) < max_supervertex_size:
                    supervertex.append(neighbor)
                    remaining_vertices.remove(neighbor)

            supervertices.append(supervertex)

    return supervertices

"""#### Function to create the edges, and assign weights to vertices and edges for every coarsened graph"""

def edge_count(C, E, node_weights):
    supervert = {}
    new_edges = {}
    supervert_weights = {}

    # Map each vertex to its supervertex and sum node weights
    for i, cluster in enumerate(C):
        cluster_weight = 0
        for node in cluster:
            supervert[node] = i
            cluster_weight += node_weights.get(node, 1)  # Default weight 1 if not specified
        supervert_weights[tuple(cluster)] = cluster_weight

    # Process edges with weights
    for u, v in E:
        su, sv = supervert[u], supervert[v]
        if su != sv:  # Inter-supervertex edge
            edge = (min(su, sv), max(su, sv))
            new_edges[edge] = new_edges.get(edge, 0) + 1  # Track weight as count
        # Intra-supervertex edges are ignored for coarsening

    return new_edges, supervert_weights

"""#### FM Partition Algorithm"""

def fmpartition(Av, E, part, st = None):
    print("Hi")
    V = len(Av)
    S = [[] for _ in range(V)]
    for he, weight in E.items():
        u, v = he
        S[u].append((v, weight))
        S[v].append((u, weight))  # This is an adjacency list creation once again.
    parti = list(part) #Deep Copy of the initial partition created.
    F = [i for i in range(V)] # To have a track of total no.of vertices
    T = []
    G = []
    Atot = sum(Av)
    skew = max(Av) #To make it flexible even while having very few vertices, this works better. The final solution will fall within the skew as well
    Amin = Atot / 2 - skew
    Amax = Atot / 2 + skew
    m = None
    costlist = cost(V, E, list(part), T)
    while len(T) != V:
        max_gain = -float("inf")
        m = None
        for i in range(len(costlist)):
            if costlist[i] is None:
                costlist[i] = -float("inf")
        for i in range(V): # Running to get the maximum cost, not violating the area balance.
            if costlist[i] is not None:
                AreaA = sum(Av[v] for v in range(V) if part[v]==1)
                # Check if moving this vertex keeps A within allowed area range
                if part[i] ==1 and Amin <= AreaA  - Av[i] <= Amax:
                    if costlist[i] >= max_gain:
                        max_gain = costlist[i]
                        m = i
                elif part[i]==0 and Amin <= AreaA + Av[i] <= Amax:
                    if costlist[i] >= max_gain:
                        max_gain = costlist[i]
                        m = i
        if m is None:
            return part
        T.append(m)
        costlist[m] = None
        for u, w in S[m]: #Updation in gain table due to highest gain swap
            if (part[u] and part[m]) or (not part[u] and not part[m]):
                costlist[u] += 2 * w
            elif (not part[u] and part[m]) or (part[u] and not part[m]):
                costlist[u] -= 2 * w
        if m in F:
            F.remove(m)
        else:
            break
        part[m] = not part[m]
        G.append(max_gain)
    num = 0
    s = 0
    for g in range(len(G)):
        s+=G[g]
        if G[g]<=0 and g:
            break
        else:
            num += 1
    for i in range(num): #Swapping to get the temporary minima.
        if T:
            ele = T[i]
            parti[ele] = not parti[ele]
    cut = cuts(E, parti)
    if st:
        L = sorted(st.items(), key=lambda x: x[0])
    if not st or cut < L[0][0]:
        if cut not in st:
            st[cut] = None
        st[cut] = parti
        return fmpartition(Av, E, parti, st) #Looking for better minimas
    ##if len(st) >= 5:
        ##return parti
    return parti
#P = (fmpartition(Av, {e:1 for e in E}, ipart, {}))
#print(cuts(E,P))

"""#### **Final Combination**"""

def hier_part(N,E,C,s=0.1):

    #Creating a bunch of trackers.

    Track = [[i for i in range(N)]]
    Trackw = [((i,1) for i in range(N))]
    Tracke = [{e:1 for e in E}]
    initw = {i:1 for i in range(N)}
    Edges = list(E)
    Vert = N

    # Doing all possible levels of coarsening and putting it in data structures created to track.

    for _ in range(C):
        Tab = coarser(Vert,Edges,0.006)
        Track.append(Tab)
        Vert = len(Tab)
        Edges,tw = edge_count(Tab,Edges,initw)
        initw = tw
        Trackw.append(list(tw.items()))
        Tracke.append(Edges)
    dir = Track.pop(-1)
    Av = Trackw.pop(-1)
    Avi = [v[1] for v in Av]
    hE = Tracke.pop(-1)
    part = initial_partition(len(dir),Avi)
    if C==0:
        return fmpartition([1]*N,hE,part,{})
    parti = []
    partf = []
    while Track:
        parti= fmpartition(Avi,hE,part,{})
        partf = [None]*len(Track[-1])
        #Uncoarsening and going to the previous coarsened level with newer partitions
        for a in range(len(Av)):
            for i in Av[a][0]:
                partf[i] = parti[a]
        #Setting up for next
        dir = Track.pop(-1)
        Av = Trackw.pop(-1)
        Avi = [v[1] for v in Av]
        hE = Tracke.pop(-1)
        part = partf
    return part
'''area = 0
area1 = 0
res = hier_part(V,E,2)
for i in res:
    if i:
        area+=1
    else:
        area1+=1
print(cuts(E,res))
print(area,area1)'''

"""Note: Graph best forks for N=10000,C=2, when graph edge generation is probablity 0.03. Main function is of the signature:


```
# hier_part(N,E,C,s)
```


"""