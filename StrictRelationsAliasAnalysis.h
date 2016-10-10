#ifndef __StrictRelationsAliasAnalysis_H__
#define __StrictRelationsAliasAnalysis_H__

#include "llvm/ADT/SparseBitVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Pass.h"

//#include "../RangeAnalysis/RangeAnalysis.h"
#include "include/RangeAnalysis/RangeAnalysis.h"

#include <queue>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <utility>
#include <iterator> 

#include <sstream>
#include <fstream>  

typedef InterProceduralRA<Cousot> InterProceduralRACousot;

namespace {

////////////////////////////////////////////////////////////////////////////////
// Representation of types as sequences of primitive values (now bits!)
class Primitives {
  public:
  //Holds a Primitive Layout for a determined Type
  struct PrimitiveLayout {
    Type * type;
    std::vector<int> layout;
    PrimitiveLayout(Type* ty, std::vector<int> lay) {
      type = ty;
      layout = lay;
    }
  };
  struct NumPrimitive {
    Type * type;
    int num;
    NumPrimitive(Type* ty, int n) {
      type = ty;
      num = n;
    }
  };
  std::vector<PrimitiveLayout*> PrimitiveLayouts;
  std::vector<NumPrimitive*> NumPrimitives;
  std::vector<int> getPrimitiveLayout(Type* type);
  int getNumPrimitives(Type* type);
  llvm::Type* getTypeInside(Type* type, int i);
  int getSumBehind(std::vector<int> v, unsigned int i);
};
////////////////////////////////////////////////////////////////////////////////

//Forward declarations
class WorkListEngine;
class Constraint;

void* global_variable_translator;

template <class V> class BitVectorPositionTranslator {
  std::unordered_map<V, int> v_to_i;
  std::unordered_map<int, V> i_to_v;
  unsigned next_i;
  
  public:
  bool addValue(V v) {
    if(!v_to_i.count(v)) {
      v_to_i[v] = next_i;
      i_to_v[next_i] = v;
      ++next_i;
      return true;
    } else {
      return false;
    }
  }
  
  unsigned getPosition(V v) {
    if(!(v_to_i.count(v))) addValue(v);
    return v_to_i[v];
  }
  
  V getValue(unsigned i) {
    if(i_to_v.count(i)) return i_to_v[i];
    else return NULL;
  }
    
};

class StrictRelations : public ModulePass, public AliasAnalysis {

public:
  ~StrictRelations();
  static char ID; // Class identification, replacement for typeinfo
  StrictRelations() : ModulePass(ID){}

  /// getAdjustedAnalysisPointer - This method is used when a pass implements
  /// an analysis interface through multiple inheritance.  If needed, it
  /// should override this to adjust the this pointer as needed for the
  /// specified pass info.
  virtual void *getAdjustedAnalysisPointer(AnalysisID PI) override {
    if (PI == &AliasAnalysis::ID)
      return (AliasAnalysis*)this;
    return this;
  }
  
  struct Variable;
  
  class VariableSet {
    friend class VariableSetIterator;
    
    BitVectorPositionTranslator<Variable*>* trans;
    SparseBitVector<> set;
    unsigned int size;
    
    class VariableSetIterator { 
      SparseBitVector<>::iterator it;
      VariableSet* owner;
      public:
      // Preincrement.
      inline VariableSetIterator& operator++() {
        ++it;
        return *this;
      }
   
      // Postincrement.
      inline VariableSetIterator operator++(int) {
        VariableSetIterator tmp = *this;
        ++*this;
        return tmp;
      }
   
      // Return the current set bit number.
      Variable* operator*() const {
        return owner->trans->getValue(*it);
      }
   
      bool operator==(const VariableSetIterator &RHS) const {
        return it == RHS.it;
      }
   
      bool operator!=(const VariableSetIterator &RHS) const {
        return it != RHS.it;
      }
   
      VariableSetIterator() {
      }
   
      VariableSetIterator(SparseBitVector<>::iterator It, VariableSet* Owner){
        it = It;
        owner = Owner;
      }
    };
    
    public:
    typedef VariableSetIterator iterator;
    
    void insert(Variable* v) {
      trans->addValue(v);
      set.set(trans->getPosition(v));
    }
    int count(Variable* v) {
      trans->addValue(v);
      if(set.test(trans->getPosition(v))) return 1;
      else return 0; 
    }
    
    iterator begin() {
      return iterator(set.begin(), this);
    }
    
    iterator end() {
      return iterator(set.end(), this);
    }
    
    void erase(Variable* v) {
      trans->addValue(v);
      set.reset(trans->getPosition(v));
    }
    
    VariableSet() {
      trans = (BitVectorPositionTranslator<Variable*>*) global_variable_translator;
    }
    
    bool empty() {return set.empty();}
  };
  
  struct Variable {
    const Value* v;
    VariableSet LT;
    VariableSet GT;
    VariableSet SA; 
    std::unordered_set<Constraint*> constraints;
    //Constructor inserts the variable in its SA set
    Variable(const Value* V) : v(V) { SA.insert(this); } 
    
    void printStrictRelations(raw_ostream &OS);
  };
     
  //Forward declarations
  class DepEdge;

  struct DepNode {
    const Value* v;
    std::unordered_set<DepEdge*> inedges;
    std::unordered_set<DepEdge*> outedges;
    //Types
    bool arg;
    bool unk;
    bool global;
    bool alloca;
    bool call;
    std::unordered_set<const Value*> locs;
    
    DepNode(const Value* V) : v(V) {
      arg = false; unk = false; global = false; call = false;
      mustalias = new std::unordered_set<DepNode*>();
      mustalias->insert(this);
    }
    
    static void addEdge(DepNode* in, DepNode* out, Range r){
      DepEdge* e = new DepEdge(in, out, r);
      in->inedges.insert(e);
      out->outedges.insert(e);  
    }
    static void addEdge(DepNode* in, DepNode* out, Range r, const Value* o) {
      DepEdge* e = new DepEdge(in, out, r, o);
      in->inedges.insert(e);
      out->outedges.insert(e); 
    }
  
    // function and structures for the local analysis
    DepNode *local_root;
    std::map< DepNode*, std::pair<int, Range> > path_to_root;
    void getPathToRoot();
    
    // must alias information
    std::unordered_set<DepNode*>* mustalias;
    void coalesce (DepNode*);
    
  };
  
  struct DepEdge {
    DepNode* const  in;
    DepNode* const out;
    const Range range;
    const Value* const offset;
    
    DepEdge(DepNode* In, DepNode* Out, const Range R, 
    const Value* Offset = NULL) : 
      in(In), out(Out), range(R), offset(Offset) { }
      
    static void deleteEdge(DepEdge* e){
      e->in->inedges.erase(e);
      e->out->outedges.erase(e);
      delete e;  
    }
  };


  Variable* getVariable(Value * V) {
    if(variables.count(V)) return variables.at(V);
    else return NULL;
  }
  void printAllStrictRelations(raw_ostream &OS);

  // Return variables with LT, GT, SA sets filled
  std::unordered_map<const Value*, Variable*> getResult(){ 
    return variables;
  }

  class TNode; //Forward declaration
 

  InterProceduralRACousot *RA;
  std::unordered_map<const Value*, Variable*> variables;
  std::unordered_map<const Value*, DepNode*> nodes;
  std::unordered_map<const Value*, TNode*> tNodesMap;
  std::set<TNode*> tNodes;
  WorkListEngine* wle;
            
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  
  AliasResult alias(const MemoryLocation &LocA,
                              const MemoryLocation &LocB) override;
  bool runOnModule(Module &M) override;

private:  

  bool aliastest1(const Value* p1, const Value* p2);
  bool aliastest2(const Value* p1, const Value* p2);
  bool aliastest3(const Value* p1, const Value* p2);
  
  enum CompareResult {L, G, E, N};
  CompareResult compareValues(const Value*, const Value*);
  bool disjointGEPs(const GetElementPtrInst*, const GetElementPtrInst*);
  
  // Phases
  Range processGEP(const Value*, const Use*, const Use*);
  void collectConstraintsFromModule(Module &M);
  void buildDepGraph(Module &M);
  void collectTypes();
  void propagateTypes();
  void propagateArgs(std::set<DepNode*> &args);
  void propagateGlobals(std::set<DepNode*> &globals);
  void propagateUnks(std::set<DepNode*> &unks);
  void propagateAlloca(DepNode*);


  // TGraph
  void buildTGraph(std::unordered_map<const Value*, 
                      StrictRelations::Variable*> variables, raw_ostream &OS); 
  TNode* addNode(StrictRelations::Variable* element); 
  TNode* findNode( std::unordered_map<const Value*, TNode*> tNodesMap, 
                      StrictRelations::Variable* element); 
  TNode* findNode(std::set<TNode*> tNodes, TNode* node); 
  void toDot(std::string name, raw_ostream &OS);

  //Times
  float phase1;
  float phase2;
  float phase3;
  float phases;
  float test1;
  float test2;
  float test3;

  static Primitives P;
};
////////////////////////////////////////////////////////////////////////////////

//Worklist engine declarations
class Constraint;

class WorkListEngine {
public:
  void solve();
  void add(const Constraint*);
  void push(const Constraint*);
  void printConstraints(raw_ostream &OS);
  std::unordered_map<const Constraint*, bool> getConstraints() { return constraints; }
  int getNumConstraints() { return constraints.size(); }

  //WorkListEngine is in charge of constraint deletion
  ~WorkListEngine();
  
private:
  std::queue<const Constraint*> worklist;
  std::unordered_map<const Constraint*, bool> constraints;
};

class Constraint {
protected:
  WorkListEngine * engine;
public:
  virtual void resolve() const =0;
  virtual void print(raw_ostream &OS) const =0;
  virtual ~Constraint() {}
};

////////////////////////////////////////////////////////////////////////////////
// Constraint types declaration
class RLT : public Constraint {
  StrictRelations::Variable * const left, * const right;
public:
  RLT(WorkListEngine* W, StrictRelations::Variable* L,
          StrictRelations::Variable* R) : left(L), right(R) { engine = W; };
  void resolve() const override;
  void print(raw_ostream &OS) const override;
};

class LT : public Constraint {
  StrictRelations::Variable * const left, * const right;
  bool isLeftNull;
  bool isRightNull;
public:
  LT(WorkListEngine* W, StrictRelations::Variable* L,
          StrictRelations::Variable* R, bool lSide, bool rSide) : left(L)
              , right(R) { engine = W; isLeftNull = lSide; isRightNull = rSide; };
  void resolve() const override;
  void print(raw_ostream &OS) const override;
};

class RLE : public Constraint {
  StrictRelations::Variable * const left, * const right;
public:
  RLE(WorkListEngine* W, StrictRelations::Variable* L,
          StrictRelations::Variable* R) : left(L), right(R) { engine = W; };
  void resolve() const override;
  void print(raw_ostream &OS) const override;
};

class LE : public Constraint {
  StrictRelations::Variable * const left, * const right;
  bool isLeftNull;
  bool isRightNull;
public:
  LE(WorkListEngine* W, StrictRelations::Variable* L,
          StrictRelations::Variable* R, bool lSide, bool rSide) : left(L)
            , right(R) { engine = W;  isLeftNull = lSide; isRightNull = rSide; };
  void resolve() const override;
  void print(raw_ostream &OS) const override;
};

class REQ : public Constraint {
  StrictRelations::Variable * const left, * const right;
public:
  REQ(WorkListEngine* W, StrictRelations::Variable* L,
          StrictRelations::Variable* R) : left(L), right(R) { engine = W; };
  void resolve() const override;
  void print(raw_ostream &OS) const override;
};

class EQ : public Constraint {
  StrictRelations::Variable * const left, * const right;
public:
  EQ(WorkListEngine* W, StrictRelations::Variable* L,
          StrictRelations::Variable* R) : left(L), right(R) { engine = W; };
  void resolve() const override;
  void print(raw_ostream &OS) const override;
};

class PHI : public Constraint {
  StrictRelations::Variable * const left;
  std::unordered_set<StrictRelations::Variable*> operands;
public:
  PHI(WorkListEngine* W, StrictRelations::Variable* L,
                          std::unordered_set<StrictRelations::Variable*> Operands)
                          : left(L), operands(Operands) { engine = W; };
  void resolve() const override;
  void print(raw_ostream &OS) const override;
};

////////////////////////////////////////////////////////////////////////////////

class StrictRelations::TNode {
private:
  std::unordered_set<TNode*> lessThanSet;
  std::unordered_set<TNode*> greaterThanSet;
  StrictRelations::Variable* variable;
public:
  TNode(StrictRelations::Variable*);
  ~TNode();
  
  StringRef getName(){
    return (variable->v->hasName()? variable->v->getName() : "");
  }

  const Value* getValue(){
    return variable->v;
  }

  std::unordered_set<TNode*> getSetLT();
  bool hasLT(TNode* succ);
  std::unordered_set<TNode*> getSetGT();
  bool hasGT(TNode* pred);
  void addEdgeTo(TNode *dst);
  void cloneSet(TNode* from, raw_ostream &OS);
  void clonePSet(TNode* from, raw_ostream &OS);
  void intersection(std::unordered_set<StrictRelations::Variable*> phiNode,raw_ostream &OS);

};

////////////////////////////////////////////////////////////////////////////////
// DotFile class declaration --> Export graph as a .dot file

class dotFile {
private:
  std::stringstream dot;
  std::string FunctionName;
  std::string dotName;
public:
  dotFile(std::string);
  void insertLine(std::string);
  void insertEdge(std::string, std::string);
  void toFile();
  void addVertex(const Value*);
  void addEdge(std::string, std::string);
  std::string requireName(const Value *);
  std::string recreateName(const Instruction*);

};

}


#endif
