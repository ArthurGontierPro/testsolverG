#include <set>
#include <utility>
#include <vector>
#include <algorithm>
#include <iostream>
#include <fstream>
using namespace std;

const vector<pair<int, int>> patt = {{1, 2}, {1, 3}, {1, 4}};
const vector<pair<int, int>> graph = {{1, 2}, {2, 3}, {3, 4}, {4, 1}};
const int lbx = 1, ubx = 4;
const int lbv = 1, ubv = 4;
const vector<int> rx = {1,2,3,4};
const vector<int> rv = {1,2,3,4};

vector<set<int>> vars(ubx);
vector<bool> awake(ubx);

vector<vector<int>> Apatt(ubx);
vector<vector<int>> Agraph(ubv);

vector<vector<int>> idstore1;
vector<vector<vector<int>>> idstore2; // let me ooout!
int nboolctr = 2*ubx+ubv+ubv*2*patt.size();
int idctr = nboolctr;

void print(set<int>& t){
   cout<<"{";
   for(const auto& a : t)
      cout<<a<<",";
   cout<<" }"<<endl;
}
void print(vector<int>& t){
   cout<<"[";
   for(const auto& a : t)
      cout<<a<<",";
   cout<<" ]"<<endl;
}
void print(vector<vector<int>>& t){
   for(auto a : t)
      print(a);
}
void print(vector<set<int>>& t){
   for(auto a : t)
      print(a);
}
void print(vector<vector<vector<int>>>& t){
   for(auto a : t)
      print(a);
   cout<<"------------------"<<endl;
}
void adjarr(vector<pair<int,int>> g,vector<vector<int>>& t,int ub){
   for(const auto& p : g){
      int i = p.first;
      int j = p.second;
      t[i-1].emplace_back(j);
      t[j-1].emplace_back(i);
   }
}
void init(){   
   for(int x : rx){
      for(int v : rv)
         vars[x-1].insert(v);
      awake[x-1] = false;
   }
   adjarr(patt,Apatt,ubx);
   adjarr(graph,Agraph,ubv);
}

int strat(int x){
   while(x<ubx){
      if (vars[x-1].size()==1){
         x+=1;
      } else {
         return x;
      }
   }
   return ubx+1;
}
int find(vector<bool> t,bool e){ //help me I need usefull methods on structures thank god
   for (int i = 0;i<t.size();i++)
      if (t[i]==e)
         return i;
   return t.size();
}
set<int> setIntersection(set<int> set1, vector<int> set2){
   set<int> intersection;
   for (auto value : set2)
      if (set1.find(value) != set1.end())
         intersection.insert(value);
   return intersection; 
}
bool filterimp(int x, int v){
   vector<int> xn = Apatt[x-1];
   vector<int> vn = Agraph[v-1];
   for(auto n : xn){
      int nb = vars[n-1].size();
      vars[n-1] = setIntersection(vars[n-1],vn);
      if (nb>vars[n-1].size()){
         awake[n-1] = true;
         if (vars[n-1].size()==0)
         return false;
      }
   }
   return true;
}
bool filterneq(int x, int v){
   for(auto n : rx){
      if (n!=x){
         int nb = vars[n-1].size();
         vars[n-1].erase(v);
         if (nb>vars[n-1].size()){
            awake[n-1] = true;
            if (vars[n-1].size()==0)
            return false;
         }
      }
   }
   return true;
}
bool filter(ofstream& f){
   cout<<" filtering ";
   int x = find(awake,true);
   while(x<awake.size()){
      if(vars[x].size() == 1){
         int v = *vars[x].begin();
         if (!filterneq(x+1,v)){
            cout<<"failed neq"<<endl;
            return false;
         }
         if (!filterimp(x+1,v)){
            cout<<"failed imp"<<endl;
            return false;
         }
      }
      awake[x] = false;
      x = find(awake,true);
   }
   cout<<"passed"<<endl;
   return true;
}
void writerup(vector<pair<int,int>>& path, std::ofstream& f) {
    idctr++;
    f << "u";
    for (auto& p : path) {
        f << " 1 ~x" << p.first << "_" << p.second;
    }
    f << " >= 1 ;\n";
}
bool bb(int x,vector<pair<int,int>>& path,ofstream& f){
   auto savevars = vars;
   auto saveawake = awake;
   if (!filter(f))
      return false;
   x = strat(x);
   if (x>ubx)
      return true;
   auto tmpvar = vars[x-1];
   pair<int,int> event = {0,0};
   path.emplace_back(event);
   for(auto v : tmpvar){
      cout<<" try "<<x<<"="<<v<<endl;
      set<int> vv = {v};
      vars[x-1] = vv;
      awake[x-1] = true;
      pair<int,int> event = {x,v};
      path[path.size()-1] = event;
      if (!bb(x,path,f)){
         writerup(path,f);
         vars[x-1] = tmpvar;
      } else {
         return true;
      }
   }
   path.pop_back();
   awake[x-1] = false;
   vars = savevars;
   awake = saveawake;
   return false;
}

void writeopb() {
   ofstream f;
   f.open("test.opb");
   f << "* #variable= " << ubx << " #constraint= " << nboolctr << "\n";
   for (auto x : rx) {
      for (auto v : rv) {
         f << " 1 x" << x << "_" << v;
      }
      f << " >= 1 ;\n";
      for (auto v : rv) {
         f << " -1 x" << x << "_" << v;
      }
      f << " >= -1 ;\n";
   }
   int nid = 1;
   idstore1.push_back(std::vector<int>(ubx));
   generate(idstore1[0].begin(), idstore1[0].end(), [&nid] { return nid++;});
   idstore1.push_back(std::vector<int>(ubx));
   generate(idstore1[1].begin(), idstore1[1].end(), [&nid] { return nid++;});
   for (auto v : rv) {
      for (auto x : rx) {
         f << " -1 x" << x << "_" << v;
      }
      f << " >= -1 ;\n";
   }
   idstore1.push_back(std::vector<int>(ubx));
   generate(idstore1[2].begin(), idstore1[2].end(), [&nid] { return nid++;});
   for (auto x : rx) {
      vector<vector<int>> vvec(ubv);
      idstore2.emplace_back(vvec);
      for (auto xx : Apatt[x-1]) {
         for (auto v : rv) {
               f << " 1 ~x" << x << "_" << v;
               for (auto vv : Agraph[v-1]) {
                  f << " 1 x" << xx << "_" << vv;
               }
               f << " >= 1 ;\n";
               nid += 1;
               idstore2[x-1][v-1].emplace_back(nid);
         }
      }
   }
   f.close();
}


int main(){
   init();
   writeopb();
   cout<<"=========================="<<endl;   
   ofstream f;
   f.open("test.pbp");
   if (f.is_open()) {
      f << "pseudo-Boolean proof version 1.0\n";
      f << "f " << nboolctr << "\n";
      vector<pair<int,int>> emptyv;
      if (bb(lbx, emptyv, f)) {
         cout << "\n Yay a solutions !" << endl;
         for (auto x : rx) {
               cout << "    X" << x << "=" << *vars[x-1].begin() << endl;
         }
      } else {
         cout << "\n Oh nooo, No solutions" << endl;
         f << "u >= 1 ;\n";
         f << "c " << idctr + 1;
      }
      f.close();
   } else {
      cout << "Unable to open file" << endl;
   }
   return 0;
}


/*
g++ -o solve solve.cc
./solve
veripb --trace --useColor test.opb test.pbp
*/