/*
 * Mansour-Schieber O(l^2 n^2)-time edge connectivity algorithm (Algorithm II)
 */
#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include <list>
#include <climits>
#include <ctime>
#include <chrono>
#include <utility>
#include <assert.h>

using namespace std;

#define MAXLINE       100   /* max length of input line */
#define unused		   -1
#define active          1
#define inactive        0

char line[MAXLINE]; // stores input line
int *input_file; // stores input arcs
int n, m;     // number of nodes, arcs
int flow_min; // min s-t or t-s flow

int *Gadj;     // stores position of edges in Edges vector
int *Gfirst;   // first position in Gadj

int* indegree;
int* outdegree;
int delta; // minimum indegree or outdegree of all vertices

// compute graph min degree
inline int computeDelta()
{
	int mindegree = n;
	for (int i=1; i<=n; i++) {
		if (indegree[i]<mindegree) mindegree = indegree[i];
		if (outdegree[i]<mindegree) mindegree = outdegree[i];
	}
	return mindegree;
}

// edge structures
pair <int, int> edge; // from, to
vector<pair <int, int>> Edges;
int *Flow; // flow of each edge

// return the origin x of edge (x,y)
inline int edgeFrom(int k) {
	return get<0>(Edges[k]);
}

// return the target y of edge (x,y)
inline int edgeTo(int k) {
	return get<1>(Edges[k]);
}

// if v is the origin of the edge k, then return its flow
// otherwise, return 1-flow
inline int edgeFlow(int k, int v) {
	int x = get<0>(Edges[k]);  // from node
	int y = get<1>(Edges[k]);  // to node
	int f = Flow[k];  // edge flow

	if (v == x) return f;
	if (v == y) return 1 - f;
	exit(-1); // error!
}

inline void setEdgeFlow(int k, int f) {
	Flow[k] = f;
}

// if v is the origin of the edge k, then return 1-flow
// otherwise, return flow
inline int edgeCapacity(int k, int v) {
	int x = get<0>(Edges[k]);  // from node
	int y = get<1>(Edges[k]);  // to node
	int f = Flow[k];  // edge flow

	if (v == x) return 1-f;
	if (v == y) return f;
	exit(-1); // error!
}

// v must be an endpoint of the edge k=(v,w) or k=(w,v). 
// returns w
inline int edgeOther(int k, int v) {
	int x = get<0>(Edges[k]);  // from node
	int y = get<1>(Edges[k]);  // to node

	if (v == x) return y;
	if (v == y) return x;
	exit(-1); // error!
}

/* print adjacency lists in stdout */
void printGraph() {
    printf("Printing adjacency lists\n");
    for (int i=1; i<=n; i++) {
        printf("node %d : ", i);
        for (int j=Gfirst[i]; j<Gfirst[i+1]; j++) {
			int k = Gadj[j];
			int x = get<0>(Edges[k]);  // from node
			int y = get<1>(Edges[k]);  // to node
            printf(" (%d, %d)", x,y);
        }
        printf("\n");
    }
}

/* read graph from input file */
void readGraph(const char *file) {
	/*  This function reads the graph (input file) and stores the edges in a matrix. */
    FILE *input = fopen(file, "r");
    if (!input) {
        fprintf(stderr, "6Error opening file \"%s\".\n", file);
        exit(-1);
    }

    int x, y, r;
    int p = 0;
	int rline = 1; 
    while (fgets(line, MAXLINE, input) != NULL) {
        switch (line[0]) {
            case '\n':;
            case '\0': break;
			case '#' : break;
            case 'p': if (sscanf(line, "p %d %d %d", &n, &m, &r) != 3) {
							fprintf(stderr, "5Error reading graph size (%s).\n", file);
							while(1);
							exit(-1);
						}
						input_file = new int [2*m];
						break;     
            default: if (sscanf(line, "%d	%d", &x, &y) != 2) {
							fprintf(stderr, "2Error reading graph arc (%s).\n", file);
							cout << " rline is " << rline << endl;
							exit(-1);
					  }
					  rline++;
					  input_file[p++] = x;
					  input_file[p++] = y;
					  
					  if (p>2*m) {
						fprintf(stderr, "1Error! Graph has >%d arcs.\n", m);
						exit(-1);
					  }
					  break;
			}
		}
	
    fprintf(stderr, "END reading graph (%s).\n", file);
    fclose(input);
}

void processInput() {

	/* build adjacency lists from input edges */
    
	int x,y;

	Gadj = new int[2*m];
	Gfirst = new int[n + 2];
	int* Gnext = new int[n + 2];

	Flow = new int[m];
	
	indegree = new int[n + 2];
	outdegree = new int[n + 2];

    for (int i=0; i<2*m; i++) Gadj[i] = 0;
    for (int i=0; i<=n+1; i++) Gfirst[i] = Gnext[i] = indegree[i] = outdegree[i] = 0;

    for (int k=0; k<m; k++)
    {
        x = input_file[2*k];
        y = input_file[2*k+1];
        
        outdegree[x]++;					  
        indegree[y]++;
		//printf("edge (%d,%d)\n", x, y);

        Edges.push_back(make_pair(x, y));

        Gfirst[x+1]++;
        Gfirst[y+1]++;
    }

	delta = computeDelta();
	//printf("delta = %d\n", delta);

    for (int k = 1; k <= n+1; k++) 
	{
        Gfirst[k] += Gfirst[k-1];
        Gnext[k] = Gfirst[k];        
	}

    for (int k = 0; k < m; k++)
    {
		x = get<0>(Edges[k]);  // from node
        y = get<1>(Edges[k]);  // to node
        Gadj[Gnext[x]++] = k;
        Gadj[Gnext[y]++] = k;	 
    }
    
    delete [] Gnext;
}

int* pathEdge; // path edges
bool* marked;
// find path from vertices in Oq to u in the residual network
bool findPathO(bool *Omark,  int* Oq, int last_Oq, int u) {

	//printf("FindPathO to node %d\n", u);

	assert(Omark[u] == false);

	queue <int> q; // bfs queue 
    
	for (int i = 0; i < last_Oq; i++) {
		q.push(Oq[i]);
	}

	for (int i = 0; i <= n; i++) {
		pathEdge[i] = -1;
		marked[i] = false;
	}

	while ( (!q.empty()) && (!marked[u]) ) 
    { 
        int x = q.front(); 
        q.pop(); 

        for (int i = Gfirst[x]; i < Gfirst[x + 1]; i++) 
        { 
			int k = Gadj[i];	
			int v = edgeOther(k,x);
			
			if (Omark[v]) continue; // skip edge to vertex in O
			
			int c = edgeCapacity(k, x);

			if (c > 0) {
				if (!marked[v]) {
					pathEdge[v] = k;
					marked[v] = true;
					q.push(v);
				}
			}             
        } 
    } 	
	return marked[u];
}


// find path from u to some vertex w in Iq in the residual network
// returns the first such w that is found 
// returns -1 otherwise
int findPathI(bool* Imark, int u) {

	//printf("FindPathI from node %d\n", u);

	queue <int> q; // bfs queue 
	int w = -1; // first vertex in Iq reached by the bfs

	for (int i = 0; i <= n; i++) {
		pathEdge[i] = -1;
		marked[i] = false;
	}

	q.push(u);
	marked[u] = true;

	bool reachedI = Imark[u];
	while ((!q.empty()) && (!reachedI))
	{
		int x = q.front();
		q.pop();

		for (int i = Gfirst[x]; i < Gfirst[x + 1]; i++)
		{
			int k = Gadj[i];
			int v = edgeOther(k, x);

			int c = edgeCapacity(k, x);

			if (c > 0) {
				if (!marked[v]) {
					pathEdge[v] = k;
					marked[v] = true;
					q.push(v);
					if (Imark[v]) {
						reachedI = true;
						w = v;
					}
				}
			}
		}
	}
	return w;
}


// add 1 unit to the residual flow of edge k 
// if k = (u,v) then flow of k becomes 1
// if k = (v,u) then flow of k becomes 0
inline void addResidualFlowTo(int k, int v)
{
	if (v == edgeTo(k)) setEdgeFlow(k, 1);
	if (v == edgeFrom(k)) setEdgeFlow(k, 0);
}

inline void augmentFlowO(bool *Omark, int u)
{
	int v = u;
	while (!Omark[v])
	{
		int k = pathEdge[v];
		addResidualFlowTo(k, v);
		v = edgeOther(k, v);
	}	
}

// augment flow along the residual path from u to v
inline void augmentFlowI(int u, int w)
{
	int v = w;
	while (v != u)
	{
		int k = pathEdge[v];
		addResidualFlowTo(k, v);
		v = edgeOther(k, v);
	}
}


// use FordFulkerson method to compute a flow from O to u of value at most f_max
int FordFulkersonO(bool *Omark, int *Oq, int last_Oq, int u, int f_max){

	if (Omark[u]) return f_max;

	pathEdge = new int[n+1]; // parent edge in bfs tree
	marked = new bool[n+1];

	int totalFlow = 0;
	
	// reset all flows 
	for (int k=0; k<m; k++) Flow[k]=0;

	while ( findPathO(Omark, Oq, last_Oq, u) && (totalFlow <= f_max) ) {
		augmentFlowO(Omark, u); 
		totalFlow++;
	}
	return totalFlow; 
}


// use FordFulkerson method to compute a flow from u to I of value at most f_max
int FordFulkersonI(bool* Imark, int u, int f_max) {

	if (Imark[u]) return f_max;

	pathEdge = new int[n + 1]; // parent edge in bfs tree
	marked = new bool[n + 1];

	int totalFlow = 0;

	// reset all flows 
	for (int k = 0; k < m; k++) Flow[k] = 0;

	int w;
	while ( ( (w=findPathI(Imark, u))!=-1 )  && ( totalFlow <= f_max ) ) {
		augmentFlowI(u, w);
		totalFlow++;
	}
	return totalFlow;
}

inline void updateUdegrees(queue <int> &rUq, int *outdegreeU, int *indegreeU, int *Usize)
{
	while (!rUq.empty())
	{
		int v = rUq.front();
		rUq.pop();
		(*Usize)--;
		for (int j=Gfirst[v]; j<Gfirst[v+1]; j++) {			
			int e = Gadj[j];			
			int x = get<0>(Edges[e]);  // from node		
			int y = get<1>(Edges[e]);  // to node
			
			if (x==v) indegreeU[y]--;
			if (y==v) outdegreeU[x]--;
		}
	}
}

// find a vertex u in U with maximum outdegreeU[u]
inline int findMaxOutDegreeU(int *outdegreeU, bool *Umark) {
	int x = -1;
	int max = -1;
	for (int u=1; u<=n; u++) {
		if ( (Umark[u]) && (outdegreeU[u] > max) ) {
			x = u;
			max = outdegreeU[u];
		}
	}
	return x;
}

// find a vertex u in U with maximum indegreeU[u]
inline int findMaxInDegreeU(int *indegreeU, bool *Umark) {
	int x = -1;
	int max = -1;
	for (int u=1; u<=n; u++) {
		if ( (Umark[u]) && (indegreeU[u] > max) ) {
			x = u;
			max = indegreeU[u];
		}
	}
	return x;
}

void printUdegree(bool* Umark, int* outdegreeU, int *indegreeU) {
	printf("\nU = { ");
	for (int v = 1; v <= n; v++) if (Umark[v]) printf("%d ", v);
	printf("}\n");
	for (int v = 1; v <= n; v++) if (Umark[v]) printf("outdegree[%d]=%d, indegree[%d]=%d\n", v, outdegreeU[v], v, indegreeU[v]);
}

void printDegrees() {
	printf("\n");
	for (int v = 1; v <= n; v++) printf("outdegree[%d]=%d, indegree[%d]=%d\n", v, outdegree[v], v, indegree[v]);
	printf("\n");
}

// update counters for all vertices w in U s.t. the edge (u,w) exists in G
void UpdateO(int u, int k, int *count, bool* Omark, bool* Umark, queue <int> &rUq, int *Oq, int *last_Oq) {
	Omark[u] = true;
	Oq[(*last_Oq)++] = u;
	Umark[u] = false;
	rUq.push(u);
	for (int j = Gfirst[u]; j < Gfirst[u + 1]; j++) {
		int e = Gadj[j];
		int x = get<0>(Edges[e]);  // from node		
		int y = get<1>(Edges[e]);  // to node
		if ((u == x) && Umark[y]) {
			count[y]++; // y has an edge entering from O
			if (count[y]==k) UpdateO(y, k, count, Omark, Umark, rUq, Oq, last_Oq);
		}
	}
}

// update counters for all vertices w in U s.t. the edge (w,u) exists in G
void UpdateI(int u, int k, int *count, bool* Imark, bool* Umark, queue <int> &rUq) {
	Imark[u] = true;
	Umark[u] = false;
	rUq.push(u);
	for (int j = Gfirst[u]; j < Gfirst[u + 1]; j++) {
		int e = Gadj[j];
		int x = get<0>(Edges[e]);  // from node		
		int y = get<1>(Edges[e]);  // to node
		if ((u == y) && Umark[x]) {
			count[x]++; // x has an edge entering I
			if (count[x]==k) UpdateI(x, k, count, Imark, Umark, rUq);
		}
	}
}

// test if graph k-edge connected 
bool TestEdgeConnectivity(int k) {
	
	//printf("Test Edge Connectivity, k=%d\n",k);
	
	int *count = new int [n+1]; // count edges from/to O/I

	bool *Omark = new bool[n+1]; // Omark[v] is true iff v belongs to outgoing dominating set O
	bool *Imark = new bool[n+1]; // Imark[v] is true iff v belongs to ingoing dominating set I
	
	bool *Umark = new bool[n+1]; // Umark[v] is true iff v belongs to U = V-O-{u : there is edge (v,u)}	
	int Usize = n; // size of U-set
	
	int *outdegreeU = new int [n+1];  // number of edges going to U
	int *indegreeU = new int [n+1];   // number of edges entering from U
	
	for (int v=1; v<=n; v++) {
		Omark[v] = Imark[v] = false;
		Umark[v] = true;
		outdegreeU[v] = outdegree[v];
		indegreeU[v] = indegree[v];
		count[v]=0;
	}
	//printDegrees();
	//printUdegree(Umark, outdegreeU, indegreeU);
	
	// find vertex s of maximum outdegree
	int s = 1;
	for (int v=2; v<=n; v++) {
		if (outdegree[v] > outdegree[s]) s=v;
	}
	//printf("vertex of max outdegree s = %d\n", s);

	//printUdegree(Umark, outdegreeU, indegreeU);

	// Phase 1
	//printf("\n\nPHASE 1\n\n");
	int* Oq = new int[n + 1]; // queue of outgoing dominating set O vertices 
	int last_Oq; // last occupied position in Oq 
	last_Oq = 0;
	Oq[last_Oq++] = s;
	Omark[s] = true;
	Umark[s] = false; 
	//printf("vertex %d inserted into O\n", s);
	//printf("\t vertex %d removed from U\n", s);
		
	queue <int> rUq; // queue of vertices removed from U
	UpdateO(s, k, count, Omark, Umark, rUq, Oq, &last_Oq);
	updateUdegrees(rUq, outdegreeU, indegreeU, &Usize); 
	//printUdegree(Umark, outdegreeU, indegreeU);

	int u = findMaxOutDegreeU(outdegreeU, Umark);
	
	while ( Usize > 0 )
	{
		//printf("vertex u = %d\n", u);

		int f = FordFulkersonO(Omark, Oq, last_Oq, u, k);
		//printf("\t flow from O to %d = %d\n", u, f);
		//assert(f>0);
		if (f < k) return false;
		Omark[u] = true;
		Umark[u] = false;
		Oq[last_Oq++] = u;
		//printf("vertex %d inserted into O\n", u);

		UpdateO(u, k, count, Omark, Umark, rUq, Oq, &last_Oq);
		updateUdegrees(rUq, outdegreeU, indegreeU, &Usize);
		u = findMaxOutDegreeU(outdegreeU, Umark);
	}
	//printf("Usize = %d\n", Usize);
	//printf("\t k = %d\n", k);
	
	// Phase 2
	Usize=n;
	//printf("\n\nPHASE 2\n\n");
	for (int v=1; v<=n; v++) {
		Umark[v] = true;
		outdegreeU[v] = outdegree[v];		
		indegreeU[v] = indegree[v];
		count[v]=0;
	}
	//printDegrees();
	//printUdegree(Umark, outdegreeU, indegreeU);
	Imark[s] = true;
	Umark[s] = false;
	//printf("vertex %d inserted into I\n", s);
	//printf("\t vertex %d removed from U\n", s);

	UpdateI(s, k, count, Imark, Umark, rUq); 
	updateUdegrees(rUq, outdegreeU, indegreeU, &Usize);
	u = findMaxInDegreeU(indegreeU, Umark);

	//printUdegree(Umark, outdegreeU, indegreeU);
	while ( Usize > 0 )
	{
		//printf("vertex u = %d\n", u);
		//printUdegree(Umark, outdegreeU, indegreeU);

		int f = FordFulkersonI(Imark, u, k);
		//printf("\t flow from %d to I = %d\n", u, f);
		//assert(f>0);
		if (f < k) return false;
		Umark[u] = false;
		//printf("vertex %d inserted into I\n", u);

		UpdateI(u, k, count, Imark, Umark, rUq); 
		updateUdegrees(rUq, outdegreeU, indegreeU, &Usize);
		u = findMaxInDegreeU(indegreeU, Umark);
	}
	//printf("Usize = %d\n", Usize);
	//printf("\t k = %d\n\n", k);

	return true;
}


// compute edge connectivity l provided that l<=k 
int ComputeEdgeConnectivity(int k) {
	
	//printf("Compute Edge Connectivity, k=%d\n", k);
	
	int min_k = k;
	
	int *count = new int [n+1]; // count edges from/to O/I

	bool *Omark = new bool[n+1]; // Omark[v] is true iff v belongs to outgoing dominating set O
	bool *Imark = new bool[n+1]; // Imark[v] is true iff v belongs to ingoing dominating set I
	
	bool *Umark = new bool[n+1]; // Umark[v] is true iff v belongs to U = V-O-{u : there is edge (v,u)}	
	int Usize = n; // size of U-set
	
	int *outdegreeU = new int [n+1];  // number of edges going to U
	int *indegreeU = new int [n+1];   // number of edges entering from U
	
	for (int v=1; v<=n; v++) {
		Omark[v] = Imark[v] = false;
		Umark[v] = true;
		outdegreeU[v] = outdegree[v];
		indegreeU[v] = indegree[v];
		count[v]=0;
	}
	//printDegrees();
	//printUdegree(Umark, outdegreeU, indegreeU);
	
	// find vertex s of maximum outdegree
	int s = 1;
	for (int v=2; v<=n; v++) {
		if (outdegree[v] > outdegree[s]) s=v;
	}
	//printf("vertex of max outdegree s = %d\n", s);

	//printUdegree(Umark, outdegreeU, indegreeU);

	// Phase 1
	//printf("\n\nPHASE 1\n\n");
	int* Oq = new int[n + 1]; // queue of outgoing dominating set O vertices 
	int last_Oq; // last occupied position in Oq 
	last_Oq = 0;
	Oq[last_Oq++] = s;
	Omark[s] = true;
	Umark[s] = false; 
	//printf("vertex %d inserted into O\n", s);
	//printf("\t vertex %d removed from U\n", s);
		
	queue <int> rUq; // queue of vertices removed from U
	UpdateO(s, k, count, Omark, Umark, rUq, Oq, &last_Oq);
	updateUdegrees(rUq, outdegreeU, indegreeU, &Usize); 
	//printUdegree(Umark, outdegreeU, indegreeU);

	int u = findMaxOutDegreeU(outdegreeU, Umark);
	
	while ( Usize > 0 )
	{
		//printf("vertex u = %d\n", u);

		int f = FordFulkersonO(Omark, Oq, last_Oq, u, min_k);
		//printf("\t flow from O to %d = %d\n", u, f);
		//assert(f>0);

		if (f < min_k) min_k = f;
		Omark[u] = true;
		Umark[u] = false;
		Oq[last_Oq++] = u;
		//printf("vertex %d inserted into O\n", u);

		UpdateO(u, k, count, Omark, Umark, rUq, Oq, &last_Oq);
		updateUdegrees(rUq, outdegreeU, indegreeU, &Usize);
		u = findMaxOutDegreeU(outdegreeU, Umark);
	}
	//printf("Usize = %d\n", Usize);
	//printf("\t k = %d\n", k);
	
	// Phase 2
	Usize=n;
	//printf("\n\nPHASE 2\n\n");
	for (int v=1; v<=n; v++) {
		Umark[v] = true;
		outdegreeU[v] = outdegree[v];		
		indegreeU[v] = indegree[v];
		count[v]=0;
	}
	//printDegrees();
	//printUdegree(Umark, outdegreeU, indegreeU);
	//printf("vertex of max outdegree s = %d\n", s);
	Imark[s] = true;
	Umark[s] = false;
	//printf("vertex %d inserted into I\n", s);
	//printf("\t vertex %d removed from U\n", s);

	UpdateI(s, k, count, Imark, Umark, rUq); 
	updateUdegrees(rUq, outdegreeU, indegreeU, &Usize);
	u = findMaxInDegreeU(indegreeU, Umark);

	//printUdegree(Umark, outdegreeU, indegreeU);

	while ( Usize > 0 )
	{
		//printf("vertex u = %d\n", u);
		//printUdegree(Umark, outdegreeU, indegreeU);

		int f = FordFulkersonI(Imark, u, min_k);
		//printf("\t flow from %d to I = %d\n", u, f);
		if (f < min_k) min_k = f;
		//assert(f>0);
		Umark[u] = false;
		//printf("vertex %d inserted into I\n", u);

		UpdateI(u, k, count, Imark, Umark, rUq); 
		updateUdegrees(rUq, outdegreeU, indegreeU, &Usize);
		u = findMaxInDegreeU(indegreeU, Umark);
	}
	//printf("Usize = %d\n", Usize);
	//printf("\t k = %d\n\n", k);

	return min_k;
}

int MansourSchieber2() {
	//printf("delta = %d\n", delta);
	int k;
	for (k=1; k<=delta; k*=2) {
		if (!TestEdgeConnectivity(k)) {
			//printf("\t FALSE\n");
			break;
		}
		//else printf("\t TRUE\n");
	}
	if (k > delta) k = delta;
	return ComputeEdgeConnectivity(k);
}

int main(int argc, char *argv[]){
 
	if (argc != 2) {
		printf("\n usage: %s <input file> \n\n", argv[0]);
        exit(-1);
	}
	char* file = argv[1];

	readGraph(file);	//read graph from file
	processInput();	    //build adjancecy lists
	//printGraph();
	using namespace std::chrono;
	high_resolution_clock::time_point t1 = high_resolution_clock::now();
	
	//int s = 1; // source vertex
	int flow_min = delta;  // upper bound of flow value
	int flow;
	 
	int k = MansourSchieber2();
	cout<<"edge connectivity is " << k << endl;	
		 
	high_resolution_clock::time_point t2 = high_resolution_clock::now();
	duration<double> time_span = duration_cast<duration<double>>(t2 - t1);
	std::cout << "\nRunning time " << time_span.count() << " seconds.";
	std::cout << std::endl;
	 
    return 0;	
}
