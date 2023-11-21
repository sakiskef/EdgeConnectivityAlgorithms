/*
* Compute edge connectivity by random sampling and local search 
*/
#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <assert.h>
#include <time.h>
#include <string.h>
#include <math.h>
#include <map>
#include <unordered_set>

#include<ctime>
#include <chrono>

using namespace std;

#define MAXLINE       100   /* max length of input line */
char line[MAXLINE]; /* stores input line */

int n, m; /* number of nodes, arcs */
int *input_file; // stores input arcs
FILE *output;

// Static adjacency lists
int *GFirstOut;
int *GOut;

int *ReverseGFirstOut;
int *ReverseGOut;

// Dynamic adjacency lists (for residual graph)
int *FirstTemp;
int *TargetTemp;
int *SourceTemp;
int *NextTemp;
int *BeforeTemp;

int *ReverseFirstTemp;
int *ReverseTargetTemp;
int *ReverseSourceTemp;
int *ReverseNextTemp;
int *ReverseBeforeTemp;

unordered_set<int> reversed_edge_pos;

int starting_vertex;

int *Parent; // store the tree during a DFS
int *stack_visited, stack_visited_top; // stores visited vertices
int *stack_edge_visited, stack_edge_visited_top;
int *outdegree, *indegree;
bool reverse_graph;

int min_degree;

bool is_export_output = true;
string algorithm_code = "2E-CHILP";
float avg2eccSize = 0;
string inputFileName = "";
string preText = "";
string testDate = "";
double takenTime = 0;

inline int get_next_free(int *First_param, int *Next_param){
	int ret = First_param[0];
	First_param[0] = Next_param[ret];

	return ret;
}

inline void push_next_free(int *First_param, int *Next_param, int pos){
	Next_param[pos] = First_param[0];
	First_param[0] = pos;
}

// managing temporal graphs where reversions are taking place
inline int insert_edge_to_temp_graph(int x,int y){
	int free_pos = get_next_free(FirstTemp, NextTemp);
	TargetTemp[free_pos] = y;
	SourceTemp[free_pos] = x;

	if(FirstTemp[x] == 0){
		FirstTemp[x] = free_pos;
		NextTemp[free_pos] = 0;
	}
	else{
		NextTemp[free_pos] = FirstTemp[x];
		BeforeTemp[FirstTemp[x]] = free_pos;
		FirstTemp[x] = free_pos;
	}
	return free_pos;
}

inline void delete_edge_from_temp_graph(int pos){
	int x = SourceTemp[pos];

	if(FirstTemp[x] == pos){ // if first
		FirstTemp[x] = NextTemp[pos];
		BeforeTemp[NextTemp[pos]] = 0;
	}
	else if(NextTemp[pos] == 0) { // if last
		NextTemp[BeforeTemp[pos]] = NextTemp[pos];
	}
	else{ // if in the middle
		NextTemp[BeforeTemp[pos]] = NextTemp[pos];
		BeforeTemp[NextTemp[pos]] = BeforeTemp[pos];
	}

	push_next_free(FirstTemp, NextTemp, pos);
}

inline void reverse_edge_in_temp_graph(int pos){
	int x = SourceTemp[pos];
	int y = TargetTemp[pos];

	delete_edge_from_temp_graph(pos);
	int new_pos = insert_edge_to_temp_graph(y,x);

	if(reversed_edge_pos.find(pos) != reversed_edge_pos.end()){
		reversed_edge_pos.erase(reversed_edge_pos.find(pos));
	}
	else{
		reversed_edge_pos.insert(new_pos);
	}
}

void unreverse_all_edges(){
	while(reversed_edge_pos.size()!= 0){
		// the deletion from the unordered set are happening inside the function
		reverse_edge_in_temp_graph(*reversed_edge_pos.begin());
	}
}

int edge_counter, count_threshold;

void print_graph(int *First, int *Target, int *Next, int *Source, int *reverse_edge){

	for(int i = 1; i <= n; i++){
		int k = First[i];
		printf("vertex %d:",i);

		while(k != 0){
			int v = Target[k];

			printf(" %d", v);
			if(Source[k] != i){
				exit(1);
			}
			k = Next[k];
		}
		printf("\n");
	}
}

void test_graph(){
	for(int i = 1; i <= n; i++){
		int k = FirstTemp[i];
		while(k != 0){
			if(SourceTemp[k] != i){
				printf("!!Broken Source\n");
				exit(1);
			}
			k = NextTemp[k];
		}
	}
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////check for one-edges-out-component ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


int *stack_cut_edges, stack_cut_edges_top;
int *min_cut_edges, min_cut_edges_top;

///////////////////////////////////////////////////////////////////////////////////////////

/* find path (from s to t) in the residual graph and stores it in the parent vector*/
bool BFSresidual(int s, int t){
	int *queue = stack_visited;
	int queue_head, queue_tail;
	bool found_t = false;

	queue_head = queue_tail = 0;

	queue[queue_head++] = s;
	Parent[s] = -1;

	while(queue_head != queue_tail){
		int next_to_process = queue[queue_tail++];
		// 	  printf("next to process: %d\n",next_to_process);

		int k = FirstTemp[next_to_process];
		while(k != 0){
			int v = TargetTemp[k];

			edge_counter = edge_counter+1;
			if(!Parent[v]){
				Parent[v] = k;
				queue[queue_head++] = v;
				if(v == t){
					found_t = true;
					break;
				}
			}

			k = NextTemp[k];
		}
		if(found_t) break;
	}
	stack_visited_top = queue_head;
	return found_t;
}


int FordFulkerson(int k, int num_pair_samples){
	printf("FordFulkerson k = %d, pairs = %d\n",k,num_pair_samples);
	int cut_size = -1;
	for(int i = 0; i < num_pair_samples; i++){
		int s = input_file[2*(int)(rand() % m)];
		int t = input_file[2*(int)(rand() % m)];
		while (s == t) {
			t = input_file[2*(int)(rand() % m)];
		}
		for (int j = 0; j<= k; j++){
			bool found = BFSresidual(s,t);

			if(found){
				int v = t;
				while(v != s){
					int parent_v = SourceTemp[Parent[v]];
					reverse_edge_in_temp_graph(Parent[v]);
					v = parent_v;
				}
			}
			else {
				stack_cut_edges_top = 0;

				printf("Found out component with %d vertices at iteration i = %d\n",stack_visited_top, j); fflush(0);
				for(int j = 0; j< stack_visited_top; j++){
					int v = stack_visited[j];
					for(int t = GFirstOut[v]; t < GFirstOut[v+1]; t++){
						int w = GOut[t];
						if(w != s && Parent[w] == 0){ // if not visited
							printf("cut_edge = (%d, %d)\n",v,w);
							stack_cut_edges[stack_cut_edges_top++] = v;
							stack_cut_edges[stack_cut_edges_top++] = w;
						}
					}
				}
				cut_size = stack_cut_edges_top / 2;
			}

			for(int l = 0; l < stack_visited_top; l++){
				Parent[stack_visited[l]] = 0;
			}
			stack_visited_top = 0;
			if(cut_size >= 0) break;
		}
		unreverse_all_edges();
		if(cut_size >= 0) break;
	}
	return cut_size;
}

///////////////////////////////////////////////////////////////////////////////////////////

/* depth-first search from vertex k for 2*delta+1 edges 
stores parents and labels        */

void DFS_explore(int u){
	stack_visited[stack_visited_top++] = u;
	// 	visited[u] = true;
	int k = FirstTemp[u];
	while(k != 0){
		int v = TargetTemp[k];

		if (edge_counter >=(count_threshold)){
			break;
		}

		stack_edge_visited[stack_edge_visited_top++] = k;
		edge_counter = edge_counter+1;

		if (Parent[v] == 0) {
			Parent[v] = k;
			DFS_explore(v);
		}
		k = NextTemp[k];
	}  
}

int kEdgeOut(int u, int k, int delta){

	count_threshold = (k+1) * delta;
	bool found_cut = false;
	stack_edge_visited_top = 0;
	edge_counter = 0;
	stack_cut_edges_top = 0;

	for (int i = 1; i <= k+1 && !found_cut; i++){
		stack_visited_top = 0;
		stack_edge_visited_top = 0;
		edge_counter = 0;

		Parent[u] = -1;
		DFS_explore(u);
		if(edge_counter >= count_threshold){
			// sample an edge an reverse the path on the tree to the root
			int rand_index = (int) rand() % stack_edge_visited_top;
			int v = TargetTemp[stack_edge_visited[rand_index]];
			while(v == u){ // we don't want to select an incoming edge to the root of the tree
				rand_index = (int) rand() % stack_edge_visited_top;
				v = TargetTemp[stack_edge_visited[rand_index]];
			}
			while(v != u){
				int parent_v = SourceTemp[Parent[v]];
				// // 	printf("%d-->%d (=%d), edges visited = %d\n",parent_v,v,u, stack_edge_visited_top); fflush(0);
				reverse_edge_in_temp_graph(Parent[v]);
				v = parent_v;
			}
		}
		else{ // cut found
			found_cut = true;
			stack_cut_edges_top = 0;

			// Find all edge outgoind from the component that was found
			for(int j = 0; j< stack_visited_top; j++){
				int v = stack_visited[j];
				for(int t = GFirstOut[v]; t < GFirstOut[v+1]; t++){
					int w = GOut[t];
					if(w != u && Parent[w] == 0){ // if not visited
						// printf("cut_edge = (%d, %d)\n",v,w);
						stack_cut_edges[stack_cut_edges_top++] = v;
						stack_cut_edges[stack_cut_edges_top++] = w;
					}
				}
			}
		}

		for(int j = 0; j < stack_visited_top; j++){
			Parent[stack_visited[j]] = 0;
		}
		stack_visited_top = 0;
	}
	unreverse_all_edges();
	if (found_cut) return stack_cut_edges_top/2;
	else return -1;
}

int ExploreFixedDelta(int k, int delta, int samples_num){
	int cut_size = -1;

	printf("Local Search k = %d, delta = %d, sampling = %d\n",k, delta, samples_num);
	for(int u = 1; u <= n; u++){
		bool sample_vertex;
		if(!reverse_graph){
			sample_vertex = ((double)rand()/(double)RAND_MAX) <= (double)outdegree[u] * (double)samples_num/(double)m;
		} else{
			sample_vertex = ((double)rand()/(double)RAND_MAX) <= (double)indegree[u] * (double)samples_num/(double)m;
		}
		if(!sample_vertex) continue;
		
		stack_cut_edges_top = 0;

		cut_size = kEdgeOut(u, k, delta);

		if(cut_size >= 0){
			int pos = 0;
			printf("Cut of size %d found : \n", cut_size);
			while(pos < stack_cut_edges_top){
				int x = stack_cut_edges[pos++];
				int y = stack_cut_edges[pos++];
				// printf("(%d, %d)\n",x,y);
			}
			return cut_size;
		}
	}
	// no cut was found
	return -1;
}

void SwapGraphs(){
	int* temp = FirstTemp;
	FirstTemp = ReverseFirstTemp;
	ReverseFirstTemp = temp;

	temp = TargetTemp;
	TargetTemp = ReverseTargetTemp;
	ReverseTargetTemp = temp;

	temp = SourceTemp;
	SourceTemp = ReverseSourceTemp;
	ReverseSourceTemp = temp;

	temp = NextTemp;
	NextTemp = ReverseNextTemp;
	ReverseNextTemp = temp;

	temp = BeforeTemp;
	BeforeTemp = ReverseBeforeTemp;
	ReverseBeforeTemp = temp;

	temp = GOut;
	GOut = ReverseGOut;
	ReverseGOut = temp;

	temp = GFirstOut;
	GFirstOut = ReverseGFirstOut;
	ReverseGFirstOut = temp;
	
	reverse_graph = !reverse_graph;
}

void Process(){
	int k_lower_bound = 1;
	int k_upper_bound = min_degree;
	int cut_size = -1;

	int k = 1;
	min_cut_edges_top = 0;
	// first identify a factor 2 approx of the min0cut value
	while(cut_size == -1 && k < min_degree){
		cut_size = -1;
		for (int delta = k; delta < m/(k+1); delta*=2){
			int sample_num = m/delta;
			cut_size = ExploreFixedDelta(k, delta, sample_num);
			if(cut_size >= 0){ // Store the edges of the cut
				for( int i = 0; i < stack_cut_edges_top; i++){
					min_cut_edges[i] = stack_cut_edges[i];
				}
				min_cut_edges_top = stack_cut_edges_top;
				break;
			}
			SwapGraphs();
			cut_size = ExploreFixedDelta(k, delta, sample_num);
			SwapGraphs();
			if(cut_size >= 0){ // Store the reverse edges of the cut
				for( int i = 0; i < stack_cut_edges_top; i+=2){
					min_cut_edges[i] = stack_cut_edges[i+1];
					min_cut_edges[i+1] = stack_cut_edges[i];
				}
				min_cut_edges_top = stack_cut_edges_top;
				break;
			}
		}

		if (cut_size == -1){
			cut_size = FordFulkerson(k, k*log2(m));
			if (cut_size >= 0){
				for( int i = 0; i < stack_cut_edges_top; i++){
					min_cut_edges[i] = stack_cut_edges[i];
				}
				min_cut_edges_top = stack_cut_edges_top;
			}
		}
		if (cut_size >= 0){
			k_upper_bound = cut_size;
			if(k_lower_bound > k_upper_bound) k_lower_bound = k_upper_bound;
		}
		else k_lower_bound = k+1;
		// double the size of the cut to look for
		k *= 2;
		if (k > k_upper_bound) k = k_upper_bound;
	}

	// Given an upper bound an a lower bound on k, find the min cut size
	while (k_lower_bound != k_upper_bound){
		k = (k_lower_bound + k_upper_bound) / 2;
		cut_size = -1;
		for (int delta = k; delta < m/(k+1); delta*=2){
			int sample_num = m/delta;
			cut_size = ExploreFixedDelta(k, delta, sample_num);
			if(cut_size >= 0){
				// Store the edges of the cut
				for( int i = 0; i < stack_cut_edges_top; i++){
					min_cut_edges[i] = stack_cut_edges[i];
				}
				min_cut_edges_top = stack_cut_edges_top;
				break;
			}
			SwapGraphs();
			cut_size = ExploreFixedDelta(k, delta, sample_num);
			SwapGraphs();
			if(cut_size >= 0){
				// Store the reverse edges
				for( int i = 0; i < stack_cut_edges_top; i+=2){
					min_cut_edges[i] = stack_cut_edges[i+1];
					min_cut_edges[i+1] = stack_cut_edges[i];
				}
				min_cut_edges_top = stack_cut_edges_top;
				break;
			}
		}
		if (cut_size == -1){
			cut_size = FordFulkerson(k, k*log2(m));
			if (cut_size >= 0){
				for( int i = 0; i < stack_cut_edges_top; i++){
					min_cut_edges[i] = stack_cut_edges[i];
				}
				min_cut_edges_top = stack_cut_edges_top;
			}
		}
		if (cut_size >= 0){
			k_upper_bound = cut_size;
			if(k_lower_bound > k_upper_bound) k_lower_bound = k_upper_bound;
		}
		else k_lower_bound = k+1;
	}

	printf("The min-cut has size %d:", min_cut_edges_top/2);
	for (int i = 0; i < min_cut_edges_top; i+= 2){
		printf("(%d, %d)\n", min_cut_edges[i], min_cut_edges[i+1]);
	}
}

void delete_space () {
	delete [] GFirstOut;
	delete [] GOut;
	delete [] ReverseGFirstOut;
	delete [] ReverseGOut;

	delete [] FirstTemp;
	delete [] TargetTemp;
	delete [] SourceTemp;
	delete [] NextTemp;
	delete [] BeforeTemp;

	delete [] ReverseFirstTemp;
	delete [] ReverseTargetTemp;
	delete [] ReverseSourceTemp;
	delete [] ReverseNextTemp;
	delete [] ReverseBeforeTemp;

	delete [] Parent;
	delete [] stack_visited;
	delete [] stack_edge_visited;
	delete [] stack_cut_edges;
	delete [] min_cut_edges;
}

void init() {
	FirstTemp = new int [n+2];
	TargetTemp = new int [m+2];
	SourceTemp = new int [m+2];
	NextTemp = new int [m+2];
	BeforeTemp = new int [m+2];

	ReverseFirstTemp = new int [n+2];
	ReverseTargetTemp = new int [m+2];
	ReverseSourceTemp = new int [m+2];
	ReverseNextTemp = new int [m+2];
	ReverseBeforeTemp = new int [m+2];

	Parent = new int [n+2];
	stack_visited = new int [n+2];
	stack_edge_visited = new int [m+2];
	stack_cut_edges = new int [n+2];
	min_cut_edges = new int [n+2];
	outdegree = new int [n+2];
	indegree = new int [n+2];

	for (int i = 0; i < n + 2; i++){
		FirstTemp[i] = 0;
		ReverseFirstTemp[i] = 0;
		Parent[i] = 0;
		outdegree[i] = 0;
		indegree[i] = 0;
	}

	FirstTemp[0] = 1;
	ReverseFirstTemp[0] = 1;

	for (int i = 0; i < m+2; i++){
		if(i < m+1){
			NextTemp[i] = i+1;
			ReverseNextTemp[i] = i+1;
		}
		if(i>=1){
			BeforeTemp[i] = i-1;
			ReverseBeforeTemp[i] = i-1;
		}
	}

	// Build the graph

	GOut = new int[m];
	GFirstOut = new int[n + 2];
	int *g_last_out = new int[n + 2];


	ReverseGOut = new int [m];
	ReverseGFirstOut = new int [n + 2];
	int *r_g_last_out = new int[n + 2];

	reverse_graph = false;

	g_last_out[0]  = 0;

	for (int i = 0; i <= n + 1; i++) GFirstOut[i]  = ReverseGFirstOut[i] = 0;

	int x, y;
	for (int k = 0; k < m; k++) {
		x = input_file[2 * k];
		y = input_file[2 * k + 1];
		GFirstOut[x + 1]++;
		ReverseGFirstOut[y + 1]++;
	}
	min_degree = 0;
	for (int k = 1; k <= n + 1; k++) {
		if(GFirstOut[k] > min_degree) min_degree = GFirstOut[k];
		outdegree[k] = GFirstOut[k];
		GFirstOut[k] += GFirstOut[k - 1];
		g_last_out[k] = GFirstOut[k];

		if(ReverseGFirstOut[k] > min_degree) min_degree = ReverseGFirstOut[k];
		indegree[k] = ReverseGFirstOut[k];
		ReverseGFirstOut[k] += ReverseGFirstOut[k - 1];
		r_g_last_out[k] = ReverseGFirstOut[k];
	}

	for (int k = 0; k < m; k++) {
		x = input_file[2 * k];
		y = input_file[2 * k + 1];

		GOut[g_last_out[x]++] = y;
		ReverseGOut[r_g_last_out[y]++] = x;
		insert_edge_to_temp_graph(x, y);
	}
	delete [] g_last_out;
	delete [] r_g_last_out;

	// Swap and initialize the reverse temp graph as well
	SwapGraphs();

	for (int k = 0; k < m; k++) {
		x = input_file[2 * k];
		y = input_file[2 * k + 1];

		insert_edge_to_temp_graph(y, x);
	}

	// Swap back to the forward temp graph
	SwapGraphs();
}



/* read graph from input file */
void readGraph(const char *file) {
	FILE *input = fopen(file, "r");
	if (!input) {
		fprintf(stderr, "Error opening file \"%s\".\n", file);
		exit(-1);
	}

	int x, y;
	int p = 0;

	while (fgets(line, MAXLINE, input) != NULL) {
		switch (line[0]) {
			case '\n':;
			case '\0': break;
			case 'p': if (sscanf(line, "p %d %d %d", &n, &m, &x) != 3) {
				fprintf(stderr, "Error reading graph size (%s).\n", file);
				exit(-1);
			}
			input_file = new int [2*m];
			break;
			default: if (sscanf(line, "%d	%d", &x, &y) != 2) {
				fprintf(stderr, "Error reading graph arc (%s).\n", file);
				exit(-1);
			}
			assert(x <= n);
			assert(y <= n);

			if(x == y) break;

			input_file[p++] = x;
			input_file[p++] = y;
			if (p>2*m) {
				fprintf(stderr, "Error! Graph has >%d arcs.\n", m);
				exit(-1);
			}
			break;
		}
	}
	if(p<2*m) m = p/2;
	printf("number of nodes =%d , number of edges=%d\n",n,m);
	fprintf(stderr, "END reading graph (%s).\n", file);
	fclose(input);
}

int main(int argc, char *argv[]) {
	if (argc != 2 ) {
		printf("\n usage: %s <input file>\n\n", argv[0]);
		exit(-1);
	}

	char *file = argv[1];

	readGraph(file);

	init();
	fprintf(stderr, "initialization done\n");
	fprintf(stderr, "graph was built\n");

	using namespace std::chrono;
	high_resolution_clock::time_point t1 = high_resolution_clock::now();

	srand(time(NULL));
	Process();

	high_resolution_clock::time_point t2 = high_resolution_clock::now();
	duration<double> time_span = duration_cast<duration<double>>(t2 - t1);
	std::cout << "\nRunning time " << time_span.count() << " seconds.";
	std::cout << std::endl;

	delete_space();
}
