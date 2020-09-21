

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <iostream>
#include <math.h>
#include <fstream>
#include <limits>
#include <sys/stat.h>
#include <unistd.h>
#include <ctime>
#include <typeinfo>
#include <vector>
#include<algorithm>
#include <sstream>
using namespace std;

// /* const values to control maximum sizes */
const int MaxComms = 3;
const long int Nodes = 600;

const bool DegreeCorrect = 1;
const int MAXEDGES = 10000000;  // this is the maximum number of edges

/* empty global declarations */

 // 0 means don't correct for the degrees, 1 means do correct for the degrees.
 int  Comms[Nodes];
 
 int AdjMatrix[Nodes][Nodes];
/* Number of random initializations (default) */
unsigned int KLPerNetwork = 1;

/********** GLOBAL VARIABLES **********/
bool TrueCommsAvailable = 1; // (default) Changes to 1 if user passes in true comms.
bool InitializationOption = 0; // (default) May be changed to 1 by user.

// OVERALL GENERAL VARIABLES NEEDED FOR ALL OF THE CODE
long int *AdjList[Nodes];
long int LastEmpty[Nodes];
long int Degree[Nodes];  // Degree of nodes in the network
long int EdgeList[MAXEDGES][2]; // The first is the maximum number of edges to read in

// FOR KL
unsigned int CurrentState[Nodes];
int BestState[Nodes];
int ChangeSet[Nodes];
int UpdateIndex[Nodes];
int TrueState[Nodes]; // This records the true communities if they exist read in from the file

double TwiceEdges = 0;
double MaxScore = 0;

int BestCommVertices[MaxComms];
int BestCommStubs[MaxComms];
int BestEdgeMatrix[MaxComms][MaxComms];

int CurrentCommVertices[MaxComms];
int CurrentCommStubs[MaxComms];
int CurrentEdgeMatrix[MaxComms][MaxComms];

int AdjustmentFrom[MaxComms];
int AdjustmentDestination[MaxComms];
int TempNeighborSet[2][MaxComms];  // the first entry lists the comm and the second entry lists the number of edges to that comm
int NeighborSet[2][MaxComms]; // this is what we record and use
int SelfEdgeCounter = 0; // this records self-edges to make sure that they are counted correctly
int ActualDiffComms=0; // this records the number of different comms in neighborhood

// For reporting best state
int SavedState[Nodes];
int SavedCommVertices[MaxComms];
int SavedCommStubs[MaxComms];
int SavedEdgeMatrix[MaxComms][MaxComms];
double NMIValue = 0;
double VIValue = 0;
double HighestScore = 0;

/* function declarations */
//void freegraph(); // gets rid of the graph pointers at end
void GetTheNetwork(string fileName1,string fileName2);
void RunKL(); // runs Kernighan-Lin once.
void Initialize(); // initializes the data structures for KL
double ComputeInitialScore(); // computes the initial score after initialization
void ComputeNeighborSet(int vertex, int option);  // computes the neighbor set for a vertex, using either best or currentstates
double ComputeProposal(int vertex, int from, int destination); // computes the value of the particular change
void UpdateMatrices(int vertex, int option, int from, int destination); // this updates either the best
//or current matrices based on moving the vertex from from to destination
double LogFunction(double x); // this returns x*log(x) and zero if x=0
void PrintResults(); // prints out the resulting graph for now
double ComputeVI();
double ComputeNMI();
double Entropy(int entoption);
double JointEntropy();
double Apply_method();
int maxx(std::vector<int> x);


double Apply_method()
{
  HighestScore = -numeric_limits<double>::max( );
  VIValue = 0;
  NMIValue = 0;
 
  unsigned int i,j,k,m,l;
   for(j=0; j < KLPerNetwork; j++)
   {
     RunKL();
     //KL,dt,L:
     
    if(MaxScore >= HighestScore)
    {
      HighestScore = MaxScore;
      if(TrueCommsAvailable == 1)
      {
	VIValue = ComputeVI();
	NMIValue = ComputeNMI();
	cout << "VI Value: " << VIValue << " NMI Value: " << NMIValue << endl;
      }
    
              for(i=0; i < MaxComms; i++)
              {
	          SavedCommVertices[i] = BestCommVertices[i];
	          SavedCommStubs[i] = BestCommStubs[i];
	          for(k=0; k < MaxComms; k++)
	              SavedEdgeMatrix[i][k] = BestEdgeMatrix[i][k];
               }
      for(i=0; i < Nodes; i++)
      {
	SavedState[i] = BestState[i];
      }
    }
  }
  
  // because PrintResults are written for best values we copy them
  // back over from the saved values which are the best ones.
  
             for(i=0; i < MaxComms; i++)
             {
                   BestCommVertices[i] = SavedCommVertices[i];
                   BestCommStubs[i] = SavedCommStubs[i];
                   for(k=0; k < MaxComms; k++)
                       BestEdgeMatrix[i][k] = SavedEdgeMatrix[i][k];
              }
  for(i=0; i < Nodes; i++)
  {
    BestState[i] = SavedState[i];
  }
  cout << "Final Score: " << ComputeInitialScore() << endl;
  
  
      
         for(i=0; i < MaxComms; i++)
         {
             for(j=0; j < MaxComms; j++)
                  cout<< BestEdgeMatrix[i][j]<<' ';
             cout<<endl; 
         }
         cout<<endl; 
     
 
  
  
  //freegraph();
  
  return NMIValue;
}



// This function deletes the graph from memory.
//void freegraph()
//{
  //long int i;//-Wunused,j;
  
  //for(i=0; i < Nodes; i++)
    //delete [] AdjList[i];
  
  //return;
//}

void RunKL()
{
  unsigned int i,j,k,m,l;
  int MaxIndex = 1;
  double CurrentScore;  // records the current log-likelihood
  int MaxVertex;  // this records the index of the largest vertex ratio found so far
  double MaxRatio;  // records the value of the ratio, actually it's the log of the ratio
  int MaxPriority; // records the community that the vertex wants to go to
  long int tempvertex = 0;
  
  double prevMaxScore = -numeric_limits<double>::max( );
  long double tolerance = 0.00000001; // this prevents loops due to numerical errors.
  
  double ProposalRatio;
  double value;
  int Priority;
  
  
  
  // This returns the log of the initial score
  MaxScore = ComputeInitialScore();
  int iter = 0;
  int maxIter = 100;
  while(MaxScore >= prevMaxScore + tolerance && iter < maxIter)
  {
    iter++;
    cout << "MAX SCORE IS: " << MaxScore << endl;
    // we start with everything equal to the best values
    CurrentScore = MaxScore;
    prevMaxScore = MaxScore;
    MaxIndex = -1;
    
    // ChangeSet records which vertices are able to move, in that they haven't
    // already moved during this KL step.  Update index will tell when the vertex
    // was chosen to move.
    for(i=0; i < Nodes; i++)
    {
      CurrentState[i] = BestState[i];
      ChangeSet[i] = i;
      UpdateIndex[i] = -1;
    }
    
  
             for(i=0; i < MaxComms; i++)
             {
                  CurrentCommVertices[i] = BestCommVertices[i];
                  CurrentCommStubs[i] = BestCommStubs[i];
                  for(j=0; j < MaxComms; j++)
	               CurrentEdgeMatrix[i][j] = BestEdgeMatrix[i][j];
             }
    
    // This loop moves each vertex once
    // Note that we DONT reinitialize changeset as this is unnecessary
    // This would make it a factor of 2 slower.
    for(i=0; i < Nodes; i++)
    {
      MaxVertex = 0;
      MaxRatio = -numeric_limits<double>::max( );
      MaxPriority = 0;
      // This loop selects which vertex to move
      for(j=0; j < Nodes-i; j++)
      {
	// get proposal and proposal ratio for ChangeSet[j]
	Priority = 0;
	ProposalRatio = -numeric_limits<double>::max( );
	// we first compute the neighbor set of the vertex, this is fixed
	// and the same for every change,
	// computing this first makes this more efficient
	// zero indicates run with current communities
	ComputeNeighborSet(ChangeSet[j], 0);
	
	// DanLarremore Modification:
	// We actually don't want to try all the comms, because some of them are forbidden.
	// We only get to choose from the entries of Comms[Types[j]].
	
	for (unsigned int k=0; k < MaxComms ; ++k)
	{
	  
	  // we compute the value of vertex ChangeSet[j] going to k
	  // we DONT allow a vertex to remain where it was
	  // This is essential to enforce so that it will go downhill and not be greedy
	  if(k != CurrentState[ChangeSet[j]])
	  {
	    value = ComputeProposal(ChangeSet[j], CurrentState[ChangeSet[j]], k);
	    if(value > ProposalRatio)
	    {
	      Priority = k;
	      ProposalRatio = value;
	    }
	  }
	}
	
	// check whether its higher than what you already have as the max KL move
	if(ProposalRatio > MaxRatio)
	{
	  MaxVertex = j;  // Note this is not the vertex j, but the vertex given by ChangeSet[j]
	  MaxRatio = ProposalRatio;
	  MaxPriority = Priority;
	}
      }
      // now we move it, first recording the current neighbors so that
      // we can update the matrices properly
      ComputeNeighborSet(ChangeSet[MaxVertex], 0);
      // This updates the matrices to represent the vertices new state
      UpdateMatrices(ChangeSet[MaxVertex], 0, CurrentState[ChangeSet[MaxVertex]], MaxPriority);
      CurrentState[ChangeSet[MaxVertex]] = MaxPriority;
      // we are using logs so we add the maxratio to the current score for the new score
      CurrentScore = CurrentScore + MaxRatio;
      UpdateIndex[ChangeSet[MaxVertex]] = i;
      // we switch it with the last element of changeset, removing it from further consideration
      // until we have moved the other vertices
      tempvertex = ChangeSet[MaxVertex];
      ChangeSet[MaxVertex] = ChangeSet[Nodes-i-1];
      ChangeSet[Nodes-i-1] = tempvertex;
      
      // now if the new state is better than the previous best state we record this
      // MaxIndex in combination with UpdateIndex
      // telling us where we are in the movement of vertices
      if(CurrentScore > MaxScore)
      {
	MaxScore = CurrentScore;
	MaxIndex = i;
      }
    }
    
    
    // now we update BestState if a change resulted in a higher maximum
    // by implementing all the changes found above
    
    // There is a potential for speeding this up here.
    if(MaxIndex != -1)
    {
      for(i=0; i < Nodes; i++)
      {
	// we only make the changes to beststate that happened before or equal to maxindex
	// no other vertex is updated
	// fortunately the update order is irrelevant to the final result so
	// we can just do it this way
	// Because we force all moves to be different, these updates are all a switch of community
	if(UpdateIndex[i] <= MaxIndex)
	{
	  // the option 1 does update corresponding to the best states / matrices
	  ComputeNeighborSet(i, 1);
	  UpdateMatrices(i, 1, BestState[i], CurrentState[i]); // 1 does best matrix update
	  BestState[i] = CurrentState[i];
	}
      }
    }
    
  }
  if (iter==maxIter)
  {
    cout << "...maxIterations on this KL run." << endl;
  }
  
  return;
}

// This starts off from a random initial condition
void Initialize()
{ 
    cout<<"khar";
  unsigned int i, j,m,l;
  int neighbor;
  int sum;
  MaxScore = 0;
  NMIValue = 0;
  VIValue = 0;
  HighestScore = 0;
  
  for(i=0; i < Nodes ; i++)
      TrueState[i] = 0;
  
  for(i=0; i < Nodes ; i++)
  {
      TrueState[i] = Comms[i];
      CurrentState[i] = 0;
      BestState[i] = 0;
      ChangeSet[i] = 0;
      UpdateIndex[i] = 0;
      SavedState [i] = 0;
  }
  
  
      for(i=0; i < Nodes ; i++)
          Degree[i] = 0 ;
  
  
  for(i=0; i < Nodes ; i++)
  {     

     
      for(j=0; j < Nodes ; j++)
      {
          
           Degree[i] += AdjMatrix[i][j];
      }
  }
  
  
  
  
         for(i=0; i < MaxComms; i++)
           {
             BestCommVertices[i] = 0;
             CurrentCommVertices [i] = 0;
             SavedCommVertices [i] = 0;
             BestCommStubs[i] = 0;
             CurrentCommStubs [i] = 0;
             SavedCommStubs [i] = 0;
             for(j=0; j < MaxComms; j++)
             {
                 BestEdgeMatrix[i][j] = 0;
                 CurrentEdgeMatrix[i][j] = 0;
                 SavedEdgeMatrix[i][j] = 0;
             }
            }
  
     

      
  //srand(time(0));
  for(i=0; i < Nodes; i++)
  {
    // BestState[i] = int(numgen.nextDouble(MaxComms));   // REPLACERNG, should return 0 to MaxComms-1 in integer
    // DanLarremore Modification:
    // The initialized communities must be constrained to respect types.
    // cout << i << "," << Types[i] << endl;
    BestState[i] =  (rand() % MaxComms );
    
    if(InitializationOption == 1)
           BestState[i] = TrueState[i];
    BestCommVertices[BestState[i]]++;
    
   
        BestCommStubs[BestState[i]] += Degree[i];
  }
  cout<<"BestState=";
  for(i=0; i < Nodes; i++)
      cout<<BestState[i]<<' ';
  cout<<endl;
  // We are going to double count all edges and then divide two
  for(i=0; i < Nodes; i++)
  {
    for(j=0; j < Nodes; j++)
    {
      
      BestEdgeMatrix[BestState[i]][BestState[j]] += AdjMatrix[i][j];
      
    }
  }
  
  
      return;
}

double ComputeInitialScore()
{
  // For the running of the KL algorithm itself this does not matter as all we use
  // are whether the score increases
  // We will want this when we compare different initializations
  
  // this actually returns 1/2 the unnormalized log-likelihood listed in the paper
  
  unsigned int i,j,m,l;
  double sum = 0;
  
  
            for (i=0 ; i<MaxComms ; i++)
            {
                  if (DegreeCorrect == 1)
                      sum = sum - 2*LogFunction(double(BestCommStubs[i]));
                  if (DegreeCorrect == 0)

                     if (BestCommVertices[i] != 0)
                       sum = sum - double(BestCommStubs[i])*log(double(BestCommVertices[i]));


                  for (j=i ; j<MaxComms ; j++)

                     
                          sum = sum + LogFunction(double(BestEdgeMatrix[i][j]));
                     
                      
            }
        return sum;
}

// We compute this using the current comm matrices
// We avoid the potential pitfalls of huge intermediate numbers by adding logs together.  So we treat 0 log 0 as 0.
// We return 0 for degree zero vertices (which really shouldn't be sent into the program
// in the first place.)
// We also return 0 for from = destination cause there is no change then.
// Here we use base e.  It returns the log of the actual value.
// Again this is half of the change in the unnormalized log-likelihood listed in the paper
double ComputeProposal(int vertex, int azz, int destination)
{
  unsigned int i;//-Wunused, j, k;
  unsigned int l;
  double ratiovalue = 0;
  int fromcount = 0;
  int destcount = 0;
  
  double help1;
  double help2;
  double help3;
  
  if(azz == destination)
    return 0;
  
  // if the degree of the vertex is zero we know nothing about it
    // in this case we don't ever change its community
    // at the end we put all degree zeroes into their own group
            


      

        if (DegreeCorrect == 1)

           if (Degree[vertex] == 0)
                return 0;

        
                    for (i=0 ; i<ActualDiffComms ; i++)
                    {

                           if ((NeighborSet[0 ][ i] != azz) && (NeighborSet[0 ][i] != destination))
                           {

                                help1 = double(CurrentEdgeMatrix[azz ][NeighborSet[0 ][i]]);
                                help2 = double(CurrentEdgeMatrix[destination ][NeighborSet[0 ][i]]);
                                help3 = double(NeighborSet[1 ][i]);

                                //cout<<"kabiri1"<<endl;
                                ratiovalue = ratiovalue + (LogFunction((help1-help3)) - LogFunction(help1 ));
                                ratiovalue = ratiovalue + (LogFunction((help2+help3)) - LogFunction(help2));
                                
                                help1 = double(CurrentEdgeMatrix[NeighborSet[0 ][i]][azz ]);
                                help2 = double(CurrentEdgeMatrix[NeighborSet[0 ][i]][destination ]);
                                help3 = double(NeighborSet[1 ][i]);

                                //cout<<"kabiri1"<<endl;
                                ratiovalue = ratiovalue + (LogFunction((help1-help3)) - LogFunction(help1 ));
                                ratiovalue = ratiovalue + (LogFunction((help2+help3)) - LogFunction(help2));
                           }

                           if (NeighborSet[0 ][i] == azz)

                                  fromcount = NeighborSet[1 ][i];

                           if (NeighborSet[0 ][i] == destination)

                                  destcount = NeighborSet[1 ][i];
                    }


                    
                        //cout<<"kabiri3"<<endl;
                         help1 = double(CurrentEdgeMatrix[azz ][destination]);
                         help2 = double(fromcount - destcount);
                         ratiovalue = ratiovalue + LogFunction((help1 + help2)) - LogFunction(help1 );
                    
                         help1 = double(CurrentEdgeMatrix[destination][azz ]);
                         help2 = double(fromcount - destcount);
                         ratiovalue = ratiovalue + LogFunction((help1 + help2)) - LogFunction(help1 );

               
                    if (DegreeCorrect == 1)
                    {
                        //cout<<"kabiri5"<<endl;
                        help1 = double(CurrentCommStubs[ azz]);
                        help2 = double(Degree[vertex ]);
                        ratiovalue = ratiovalue - 2*LogFunction((help1 - help2)) + 2*LogFunction(help1);
                    }


                    if (DegreeCorrect == 0)
                    {
                        //cout<<"kabiri6"<<endl;
                         help1 = double(CurrentCommStubs[azz]);
                         help2 = double(Degree[vertex ]);


                         if ((help1 - help2) != 0)
                              ratiovalue = ratiovalue - ((help1-help2)) * log(double(CurrentCommVertices[azz]-1) );

                         if (help1 != 0)
                               ratiovalue = ratiovalue + (help1 ) * log(double(CurrentCommVertices[azz]));
                    }




                  
                        //cout<<"kabiri7"<<endl;
                         help1 = double(CurrentEdgeMatrix[azz ][azz]);
                         help2 = double(SelfEdgeCounter + 2 * fromcount);
                         ratiovalue = ratiovalue + (LogFunction((help1 - help2) ) - LogFunction(help1 )) ;
                    

                    



                    if (DegreeCorrect == 1)
                    {
                         //cout<<"kabiri9"<<endl;
                         help1 = double(CurrentCommStubs[destination]);
                         help2 = double(Degree[vertex ]);
                         ratiovalue = ratiovalue - 2*LogFunction((help1 + help2)) + 2*LogFunction(help1);
                    }


                    if (DegreeCorrect == 0)
                    {
                        //cout<<"kabiri10"<<endl;
                         help1 = double(CurrentCommStubs[destination]);
                         help2 = double(Degree[vertex ]);



                         if ((help1 + help2) != 0)
                              ratiovalue = ratiovalue - ((help1+help2)) * log(double(CurrentCommVertices[destination]+1));



                         if (help1 != 0)
                              ratiovalue = ratiovalue + (help1 ) * log(double(CurrentCommVertices[destination]));
                    }


            
                    
                        //cout<<"kabiri11"<<endl;
                         help1 = double(CurrentEdgeMatrix[destination ][destination]);
                         help2 = double(SelfEdgeCounter + 2 * destcount);
                         ratiovalue = ratiovalue + (LogFunction((help1 + help2) ) - LogFunction((help1))) ;

                    
                 
    return ratiovalue;
}

void ComputeNeighborSet(int vertex, int option)
{
  unsigned int i,j,l;//-Wunused,j;
  int neighbor;
  
  SelfEdgeCounter = 0;
  
  
  
        ActualDiffComms = 0;
 

      
 

        for (j=0 ; j<MaxComms ; j++)
        {
               NeighborSet[0][j] = j;
               NeighborSet[1][j] = 0;
        }
       

          for (j=0 ; j<MaxComms ; j++)
          {
                TempNeighborSet[0][j]=j;
                TempNeighborSet[1][j]=0;
          }
        // NOTE SINCE A SELF-EDGE SHOWS UP TWICE IN THE ADJLIST THIS DOUBLE
        // COUNTS THESE EDGES, WE RECORD THE NUMBER OF TIMES THIS HAPPENS
        // IN A SEPARATE VARIABLE AND THEN DIVIDE BY TWO

        for (i=0 ; i<Nodes ; i++)
        {
            if (i != vertex)
            {
                if (option == 0)

                     TempNeighborSet[ 1 ][ CurrentState[i]] += AdjMatrix[vertex][ i];
                if (option == 1)


                     TempNeighborSet[1 ][BestState[i]] += AdjMatrix[vertex][i];
            }
            if (i == vertex)
                 SelfEdgeCounter += AdjMatrix[vertex][ i];
        }


       
                ActualDiffComms = 0;


                for (i=0 ; i<MaxComms ; i++)
                    if (TempNeighborSet[1][i] !=0)
                    {
                   
                        NeighborSet[0][ActualDiffComms] = TempNeighborSet[0][i];
                        NeighborSet[1][ActualDiffComms] = TempNeighborSet[1][i];
                        ActualDiffComms +=1;
                    }
        
  return;
}

void UpdateMatrices(int vertex, int option, int azz, int destination)
{
  unsigned int i,l;//-Wunused,j;
  int fromcount = 0 ;
  int destcount = 0 ;
  
  

         if (option == 0)
         {
             //cout<<"abol1"<<endl;
            CurrentCommVertices[azz] -= 1;
            CurrentCommVertices[destination] += 1;
            
                 CurrentCommStubs[azz] -= Degree[vertex];
                 CurrentCommStubs[destination] += Degree[vertex];

                 for (i=0 ; i<ActualDiffComms ; i++)
                 {
                      if (NeighborSet[0][i]!= azz && NeighborSet[0][i] != destination) 
                      {
                        // do update NOTE: each community mcc' gets updated once if it had edges switch out
                        // which is correct, remembering that mcc' is symmetric and we only count c < c' here

                          CurrentEdgeMatrix[azz][NeighborSet[0][i]] -= NeighborSet[1][i];
                          CurrentEdgeMatrix[NeighborSet[0][i]][azz] -= NeighborSet[1][i];

                          CurrentEdgeMatrix[destination][NeighborSet[0][i]] += NeighborSet[1][i];
                          CurrentEdgeMatrix[NeighborSet[0][i]][destination] += NeighborSet[1][i];
                      }

                      if (NeighborSet[0][i] == azz) 
                           fromcount = NeighborSet[1][i];

                      if (NeighborSet[0][i] == destination) 
                           destcount = NeighborSet[1][i];
                 }
                 
                             CurrentEdgeMatrix[azz][azz] -= (SelfEdgeCounter + 2*fromcount);
                             CurrentEdgeMatrix[destination][destination] += (SelfEdgeCounter + 2*destcount);
                             CurrentEdgeMatrix[azz][destination] += (fromcount-  destcount);
                             CurrentEdgeMatrix[destination][azz] += (fromcount-  destcount);
               
         }
         if (option == 1)
         {
             //cout<<"abol2"<<endl;
             BestCommVertices[azz] -= 1;
             BestCommVertices[destination] += 1;
             
                   BestCommStubs[azz] -= Degree[vertex];
                   BestCommStubs[destination] += Degree[vertex];

                   for (i=0 ; i<ActualDiffComms ; i++)
                   {
                         if (NeighborSet[0][i]!= azz &&  NeighborSet[0][i]!= destination) 
                         {
                             // do update NOTE: each community mcc' gets updated once if it had edges switch out
                             // which is correct, remembering that mcc' is symmetric and we only count c < c' here

                              BestEdgeMatrix[azz][NeighborSet[0][i]] -= NeighborSet[1][i];
                              BestEdgeMatrix[NeighborSet[0][i]][azz] -= NeighborSet[1][i];

                              BestEdgeMatrix[destination][NeighborSet[0][i]] += NeighborSet[1][i];
                              BestEdgeMatrix[NeighborSet[0][i]][destination] += NeighborSet[1][i];

                         }
                         if (NeighborSet[0][i]==azz) 
                                fromcount = NeighborSet[1][i];

                         if (NeighborSet[0][i]== destination)
                                destcount = NeighborSet[1][i];
                   }
                   
                                 BestEdgeMatrix[azz][azz] -= (SelfEdgeCounter + 2*fromcount);
                                 BestEdgeMatrix[destination][destination] += (SelfEdgeCounter + 2*destcount);
                                 BestEdgeMatrix[azz][destination] += (fromcount-  destcount);
                                 BestEdgeMatrix[destination][azz] += (fromcount-  destcount);
                   
         }
  return;
}

// This function returns zero if x = 0, otherwise it returns x*log(x)
double LogFunction(double x)
{
  if(x < 0)
  {
    
    cout<<"SOMETHING WRONG HAS OCCURRED STOP!"<< x <<"   is below zero:"  <<endl;
    
  }
  
  if(x == 0)
  {
    return 0;
  }
  
  return x*log(x);
}

// We do not normalize VI here.
double ComputeVI()
{
  double EntropyA;
  double EntropyB;
  double EntropyAB;
  
  EntropyA = Entropy(0); // 0 calls for best state
  EntropyB = Entropy(1); // 1 calls for true state
  EntropyAB = JointEntropy(); // does joint for best / true
  
  return 2*EntropyAB-EntropyA-EntropyB;
}

double ComputeNMI()
{
  double EntropyA;
  double EntropyB;
  double EntropyAB;
  
  EntropyA = Entropy(0);
  EntropyB = Entropy(1);
  EntropyAB = JointEntropy();
  cout<<"EntropyA ="<<EntropyA <<endl;
  cout<<"EntropyB ="<<EntropyB <<endl;
  cout<<"EntropyAB ="<<EntropyAB <<endl;
  return 2*(EntropyA+EntropyB-EntropyAB)/(EntropyA+EntropyB);
}

double Entropy(int entoption)
{
  cout<<"hosh1"<<endl;
  double Ent = 0;
  
  unsigned int i, j;//-Wunused, k;
  double *Ni;
  
  Ni = new double [MaxComms];
  
  for(i = 0; i < MaxComms; i++)
  {
    Ni[i] = 0;
  }
  
  for(j=0; j < Nodes; j++)
  {
    if(entoption == 0)
      Ni[BestState[j]]++;
    if(entoption == 1)
      Ni[TrueState[j]]++;
  }
  
  // NOTE WE RETURN THE ENTROPY IN LOG BASE 2
  for(i=0; i < MaxComms; i++)
  {
    if(Ni[i] != 0)
    {
      Ent = Ent - (Ni[i]/double(Nodes))*(log(Ni[i]/double(Nodes))/log(2));
    }
  }
  
  for(i=0; i < MaxComms; i++)
       cout<<Ni[i]<<' ';
  cout<<endl;
  delete [] Ni;
  
  return Ent;
}

// Calculates the joint entropy
double JointEntropy()
{
  unsigned int i, j, l;
  double JointEnt = 0;
  //double *Nij;
  //Nij = new double [MaxComms][MaxComms];
  double  Nij[MaxComms][MaxComms];
  
  // This rapidly calculates Nij in a simple fashion.
  for(i=0; i < MaxComms; i++)
  {
    for(j=0; j < MaxComms; j++)
    {
      Nij[i][j] = 0;
    }
  }
  
  for(l=0; l < Nodes; l++)
  {
    Nij[BestState[l]][TrueState[l]]++;
  }
  
  JointEnt = 0;
  for(i=0; i < MaxComms; i++)
  {
    for(j = 0; j < MaxComms; j++)
    {
      if(Nij[i][j] != 0)
      {
	// divide by log 2 to convert to base 2.
	JointEnt = JointEnt - (Nij[i][j]/double(Nodes))*(log(Nij[i][j]/double(Nodes))/log(2));
      }
    }
  }
  cout<<"hosh2"<<endl;
  for(i=0; i < MaxComms; i++)
  {
      for(j=0; j < MaxComms; j++)
         cout<<Nij[i][j]<<' ';
      cout<<endl;
  }
  cout<<endl;
  //delete [] Nij;
  return JointEnt;
}

/***** CPP ONLY *****/
void GetTheNetwork(string fileName1,string fileName2)
{
    
int i,j;
//int x;
//std::ifstream csv1(fileName1);
//std::string line1;


//if (csv1.is_open())
//{
//        for (std::string row_line1; std::getline(csv1, row_line1);)
//        {
//            AdjMatrix.emplace_back();
//            std::istringstream row_stream1(row_line1);
//            for(std::string column1; std::getline(row_stream1, column1, ',');)
//            {
//                std::stringstream convertor(column1);
//            
//                convertor >> x;
//                AdjMatrix.back().push_back(x);
//            }
//        }
//}
//else {
//    cout << "Unable to open file";
//}
//
//std::ifstream csv2(fileName2);
//std::string line2;


//if (csv2.is_open())
//{
//        for (std::string row_line2; std::getline(csv2, row_line2);)
//        {
            
//            std::istringstream row_stream2(row_line2);
//            for(std::string column2; std::getline(row_stream2, column2, ',');)
//            {
//                std::stringstream convertor(column2);
                
//                convertor >> x;
//                Comms.push_back(x);
//            }
//        }
//}
//else {
//    cout << "Unable to open file";
//} 

//std::ifstream csv3(fileName3);
//std::string line3;


//if (csv3.is_open())
//{
//        for (std::string row_line3; std::getline(csv3, row_line3);)
//        {
//            
//            std::istringstream row_stream3(row_line3);
//            for(std::string column3; std::getline(row_stream3, column3, ',');)
//            {
//                std::stringstream convertor(column3);
                
//                convertor >> x;
//                Types.push_back(x);
//            }
//        }
//}
//else {
//    cout << "Unable to open file";
//} 
std::ifstream file1(fileName1);
if (file1.is_open())
    for(int row = 0; row < Nodes; row++)
    {
        std::string line1;
        std::getline(file1, line1);
        if ( !file1.good() )
            break;

        std::stringstream iss1(line1);

        for (int col = 0; col < Nodes; col++)
        {
            std::string val1;
            std::getline(iss1, val1, ',');
            //if ( !iss1.good() )
                //break;

            std::stringstream convertor(val1);
            convertor >> AdjMatrix[row][col];
        }
    }
else 
   cout << "Unable to open file";


std::ifstream file2(fileName2);
if (file2.is_open())
    for(int row = 0; row < Nodes; row++)
    {
        std::string line2;
        std::getline(file2, line2);
        if ( !file2.good() )
            break;

        std::stringstream iss2(line2);

        for (int col = 0; col < 1; col++)
        {
            std::string val2;
            std::getline(iss2, val2, '\n');
            //if ( !iss2.good() )
                //break;

            std::stringstream convertor(val2);
            convertor >> Comms[row];
        }
    }
else 
   cout << "Unable to open file";





for(i=0 ; i<Nodes ; i++)
{
    for(j=0 ; j<Nodes ; j++)
        cout<<AdjMatrix[i][j]<<' ';
    cout<<endl;
}
for(j=0 ; j<Nodes ; j++)
        cout<<Comms[j]<<' ';
cout<<endl;


    //Initialize();
    return;
}

void PrintResults()
{
    int i;
    for (i=0 ; i< Nodes ; i++) 
        
        cout << i << "    " << BestState[i] << endl;

    if (TrueCommsAvailable == 1)
    {
        cout << "correct communities" << endl;;
        for (i=0 ; i< Nodes ; i++) 
            
            cout << i << "    " << TrueState[i] << endl;
    }

    cout <<"VI Value: " << VIValue << " NMIValue: " << NMIValue << " (Prop.) Log-Likelihood: " << HighestScore << endl ;



    
    
    return;
}

int maxx(std::vector<int> x)
{
    int i;
    int ma=x[0];
    for(i=0 ; i<x.size() ;i++)
    {
       if (x[i]>ma)
           ma= x[i];
    }
    return ma;
}


