/*
 * Compute edge connectivity by running the Ford-Fulkerson method for v1-v2, v2-v3, ..., vn-v1
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
#include <vector>
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
    
    delta = computeDelta();
		
    delete [] Gnext;
}

int* pathEdge; // path edges
bool* marked;
/* execute a breadth-first search to find a path from s to t */
bool findPath(int s, int t) {

	std::queue <int> q; // bfs queue 
    q.push(s);

	for (int i = 0; i <= n; i++) {
		pathEdge[i] = -1;
		marked[i] = false;
	}
	marked[s] = true;

	while ( (!q.empty()) && (!marked[t]) ) 
    { 
        int u = q.front(); 
        q.pop(); 

        for (int i = Gfirst[u]; i < Gfirst[u + 1]; i++) 
        { 
			int k = Gadj[i];	
			int v = edgeOther(k,u);
			int c = edgeCapacity(k, u);

			if (c > 0) {
				if (!marked[v]) {
					pathEdge[v] = k;
					marked[v] = true;
					q.push(v);
				}
			}             
        } 
    } 	
	return marked[t];
}

// add 1 unit to the residual flow of edge k 
// if k = (u,v) then flow of k becomes 1
// if k = (v,u) then flow of k becomes 0
inline void addResidualFlowTo(int k, int v)
{
	if (v == edgeTo(k)) setEdgeFlow(k, 1);
	if (v == edgeFrom(k)) setEdgeFlow(k, 0);
}

inline void augmentFlow(int s, int t)
{
	int v = t;
	while (v != s)
	{
		int k = pathEdge[v];
		addResidualFlowTo(k, v);
		v = edgeOther(k, v);
	}	
}

// use FordFulkerson method to compute a flow from s to t of value at most f_max
int FordFulkerson(int s, int t, int f_max){

	if (s == t) return -1;

	pathEdge = new int[n+1]; // parents in bfs tree
	marked = new bool[n+1];

	int totalFlow = 0;
	
	// reset all flows 
	for (int k=0; k<m; k++) Flow[k]=0;

	while ( (findPath(s,t)) && (totalFlow <= f_max) ) {
		augmentFlow(s, t); 
		totalFlow++;
	}
	return totalFlow; 
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
	
	int s = 1; // source vertex
	int flow_min = delta;  // upper bound of flow value
	int flow;
	  	
	//compute max flow from vi to v{i+1}, for i=1,..,n, and keep the minimum	 
	for (int i = 1; i < n; i++ ){
		flow = FordFulkerson(i,i+1,flow_min);	//compute max flow from i to i+1
		//printf("flow from %d to %d = %d\n", i, i+1, flow);
		if (flow < flow_min) flow_min = flow; //keep minimum
	}
	flow = FordFulkerson(n,1,flow_min);	//compute max flow from n to 1
	//printf("flow from %d to %d = %d\n", n, 1, flow);
	if (flow < flow_min) flow_min = flow; //keep minimum
	cout<<"min flow is "<<flow_min<<endl;	
		 
	high_resolution_clock::time_point t2 = high_resolution_clock::now();
	duration<double> time_span = duration_cast<duration<double>>(t2 - t1);
	std::cout << "\nRunning time " << time_span.count() << " seconds.";
	std::cout << std::endl;
	 
    return 0;	
}
