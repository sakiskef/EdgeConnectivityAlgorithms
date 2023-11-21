/*
* Compute edge connectivity by running the algorithm of Dinic for v1-v2, v2-v3, ..., vn-v1
*/
#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include <list>
#include <climits>
#include<ctime>
#include <chrono>
#include <vector>
#include <utility>

#define MAXLINE       100   /* max length of input line */
#define unused		   -1
#define active          1
#define inactive        0

using namespace std;

char line[MAXLINE]; /* stores input line */
int *input_file; // stores input arcs
int n, m; // number of nodes, arcs
int r, flow_min; // root vertex
int *Gout, *GfirstOut; // adjacency list
int *Gin, *GfirstIn; // reverce adjacency list
int delta;

int *level;
int *capacity;
int *Gadj;     // stores position of edges in Edges vector
int *Gfirst;   // first position in Gadj
int *Flow;
int *indegree;
int *outdegree;

pair<int, int> edge; // from, to
vector<pair<int, int>> Edges;

/* print adjacency lists in stdout */
void printGraph(int *nodelist, int *first, int N) {
	printf("Printing adjacency lists\n");
	for (int i = 1; i <= N; i++) {
		printf("node %d : ", i);
		for (int j = first[i]; j < first[i + 1]; j++) {
			printf("%d", nodelist[j]);
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

	int x, y;
	int p = 0;

	while (fgets(line, MAXLINE, input) != NULL) {
		switch (line[0]) {
		case '\n':
			;
		case '\0':
			break;
		case '#':
			break;
		case 'p':
			if (sscanf(line, "p %d %d %d", &n, &m, &r) != 3) {
				fprintf(stderr, "5Error reading graph size (%s).\n", file);
				exit(-1);
			}
			input_file = new int[2 * m];
			break;
		default:
			if (sscanf(line, "%d	%d", &x, &y) != 2) {
				fprintf(stderr, "2Error reading graph arc (%s).\n", file);
				exit(-1);
			}
			input_file[p++] = x;
			input_file[p++] = y;
			if (p > 2 * m) {
				fprintf(stderr, "1Error! Graph has >%d arcs.\n", m);
				exit(-1);
			}
			break;
		}
	}

	fprintf(stderr, "END reading graph (%s).\n", file);
	fclose(input);
}
inline int computeDelta() {
	int mindegree = n;
	for (int i = 1; i <= n; i++) {
		if (indegree[i] < mindegree)
			mindegree = indegree[i];
		if (outdegree[i] < mindegree)
			mindegree = outdegree[i];
	}
	return mindegree;
}

int *Gstart; // keep starting position of Gadj used in sendFlow

void processInput() {

	/* build adjacency lists from input edges */

	int x, y;

	Gadj = new int[2 * m];
	Gfirst = new int[n + 2];
	Gstart = new int[n + 2];
	int *Gnext = new int[n + 2];

	capacity = new int[m];
	level = new int[n + 1];
	
	for (int i = 0; i < m; i++) capacity[i] = 1;

	indegree = new int[n + 2];
	outdegree = new int[n + 2];

	for (int i = 0; i < 2 * m; i++)
		Gadj[i] = 0;
	for (int i = 0; i <= n + 1; i++)
		Gfirst[i] = Gnext[i] = indegree[i] = outdegree[i] = 0;

	for (int k = 0; k < m; k++) {
		x = input_file[2 * k];
		y = input_file[2 * k + 1];

		//printf("edge (%d,%d)\n", x, y);

		Edges.push_back(make_pair(x, y));

		outdegree[x]++;
		indegree[y]++;

		Gfirst[x + 1]++;
		Gfirst[y + 1]++;
	}

	for (int k = 1; k <= n + 1; k++) {
		Gfirst[k] += Gfirst[k - 1];
		Gnext[k] = Gfirst[k];
	}

	for (int k = 0; k < m; k++) {
		x = get < 0 > (Edges[k]);  // from node
		y = get < 1 > (Edges[k]);  // to node
		Gadj[Gnext[x]++] = k;
		Gadj[Gnext[y]++] = k;
	}

	delta = computeDelta();

	delete[] Gnext;

}

inline int edgeOther(int k, int v) {
	int x = get < 0 > (Edges[k]);  // from node
	int y = get < 1 > (Edges[k]);  // to node

	if (v == x)
		return y;
	if (v == y)
		return x;
	exit(-1); // error!
}
inline int edgeCapacity(int k, int v) {
	int x = get < 0 > (Edges[k]);  // from node
	int y = get < 1 > (Edges[k]);  // to node
	int c = capacity[k];  // edge flow

	if (v == x)
		return c;
	if (v == y)
		return 1 - c;
	exit(-1); // error!
}

bool Bfs(int s, int t) {

	for (int i = 1; i <= n; i++)
		level[i] = -1;
	level[s] = 0;

	std::queue<int> q; // bfs queue
	q.push(s);

	while (!q.empty()) {
		int u = q.front();
		q.pop();
		Gstart[u] = Gfirst[u]; // initialize starting position 

		if (u == t) break;

		for (int i = Gfirst[u]; i < Gfirst[u + 1]; i++) {
			int k = Gadj[i];
			int j = edgeOther(k, u);
			int c = edgeCapacity(k, u);

			if (level[j] < 0 && c > 0) {
				// Level of current vertex is, 
				// level of parent + 1 
				level[j] = level[u] + 1;
				q.push(j);
			}
		}
	}
	if (level[t] < 0)
		return false;
	else
		return true;
}

inline void setCapacity(int k, int u, int v) {
	int x = get < 0 > (Edges[k]);  // from node
	int y = get < 1 > (Edges[k]);  // to node

	//if (x == u && y == v){
	if (x == u) {
		capacity[k] = 0;
	} else {
		capacity[k] = 1;
	}
}

int sendUnitFlow(int u, int t) {

	if (u == t) return 1;

	for (int i = Gstart[u]; i < Gfirst[u + 1]; i++) {

		Gstart[u]++;

		int k = Gadj[i];
		int j = edgeOther(k, u);
		int c = edgeCapacity(k, u);

		if ((j != t) && (level[j] >= level[t])) continue;

		if (level[j] == level[u] + 1 && c > 0) {

			int temp_flow = sendUnitFlow(j, t);

			if (temp_flow > 0) {

				setCapacity(k, u, j);

				return temp_flow;

			} else {
				level[j] = 0;
			}

		}
	}

	return 0;
}

int DinicMaxFlow(int s, int t) {

	if (s == t)
		return -1;

	int total = 0;

	//initialize capacities of edges to 1
	for (int i = 0; i < m; i++) {
		capacity[i] = 1;
	}


	while (Bfs(s, t) == true) {

		while (int flow = sendUnitFlow(s, t)) {

			total += flow;
			if (total >= flow_min)
				return flow_min;
		}
	}
	return total;
}

int main(int argc, char *argv[]) {

	if (argc != 2) {
		printf("\n usage: %s <input file> \n\n", argv[0]);
		exit(-1);
	}
	char *file = argv[1];

	readGraph(file);			//reading graph from file
	processInput();			//building adjancecy lists

	using namespace std::chrono;
	high_resolution_clock::time_point t1 = high_resolution_clock::now();

	int s = 1;
	int res;

	flow_min = delta;

	//compute max flow from vi to v{i+1}, for i=1,..,n, and keep the minimum	 
	for (int i = 1; i < n; i++) {
		res = DinicMaxFlow(i, i+1);	 //compute max flow from i to i+1
		//cout << "flow from " << i << " to " << i+1 << " is " << res << endl;
		if (res < flow_min)
			flow_min = res;
	}
	res = DinicMaxFlow(n, 1);  // compute max flow from n to 1
	//cout << "flow from " << n << " to " << 1 << " is " << res << endl;
	if (res < flow_min)
		flow_min = res;

	high_resolution_clock::time_point t2 = high_resolution_clock::now();
	duration<double> time_span = duration_cast<duration<double>>(t2 - t1);
	std::cout << "\nRunning time " << time_span.count() << " seconds.";
	std::cout << std::endl;

	cout << "\nedge connectivity is " << flow_min << endl;

	return 0;
}
