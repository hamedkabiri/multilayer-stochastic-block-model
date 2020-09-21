

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
#include <vector>
#include<algorithm>
#include <sstream>
#include <typeinfo>
#include "two_oneLayer.h"



using namespace std;
string trueCommsName;

int main(int argc, char *argv[])
{
    srand(time(NULL));
    int N,K,i,j;
    N=50;
    K =4;
    
    double Values[N] ;
    double Aves[N] ;
    for (i=0 ; i<N ; i++)
    {
        Aves[i] = 0;
    }
    ofstream outfile;
    outfile.open("result.csv");
    
    for (i=0 ; i<K ; i++)
    {
        
        for (j=0 ; j<N ; j++)
        {
            Values[i] = 0;
        }
    // Read in the network
    std::string s = std::to_string(i);
    GetTheNetwork("Data" + s + ".csv","DataCommu.csv");
    
    for (j=0 ; j<N ; j++)
    {
        Initialize();

        Values[j] = Apply_method();
  
        cout<<"ASLI= "<<Values[j]<<endl;
        Aves[i] += Values[j];
        PrintResults();
        //freegraph();
        outfile<<Values[j]<< ",";
    }
    outfile<<endl;
    Aves[i] = Aves[i]/N;
    cout<<"Average="<<Aves[i]<<endl;
    }
    
    
    for (i=0 ; i<N ; i++)
    {
        outfile<<Aves[i]<< ","; 
    }
    outfile<<endl;
    outfile.close();
    return 0;
}
