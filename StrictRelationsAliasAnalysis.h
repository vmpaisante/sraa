#ifndef __StrictRelationsAliasAnalysis_H__
#define __StrictRelationsAliasAnalysis_H__

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Pass.h"

#include "../RangeAnalysis/RangeAnalysis.h"

#include <queue>
#include <set>
#include <map>
#include <utility>

typedef InterProceduralRA<Cousot> InterProceduralRACousot;

namespace {

//Forward declarations
class WorkListEngine;
class Constraint;
class DepGraph;

/// Representation of types as sequences of primitive values (now bits!)
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

class StrictRelations : public ModulePass, public AliasAnalysis {

public:
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

  struct Variable {
    const Value* v;
    std::set<Variable*> LT;
    std::set<Variable*> GT;
    std::set<Constraint*> constraints;
    Variable(const Value* V) : v(V) { }
  };

  Variable* getVariable(Value * V) {
    if(variables.count(V)) return variables.at(V);
    else return NULL;
  }
 
private:
  InterProceduralRACousot *RA;
  std::map<const Value*, Variable*> variables;
  WorkListEngine* wle;
  DepGraph* dg;
  
  // Function that collects comparisons from the instructions in the module
  void collectConstraintsFromModule(Module &M);
  Range processGEP(const Value*, const Use*, const Use*);
  void buildDepGraph(Module &M);
  enum CompareResult {L, G, E, N};
  CompareResult compareValues(const Value*, const Value*);
  CompareResult compareGEPs(const GetElementPtrInst*, const GetElementPtrInst*);
  void collectConstraintsFromDepGraph();
      
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  bool runOnModule(Module &M) override;
  AliasResult alias(const MemoryLocation &LocA,
                              const MemoryLocation &LocB) override;

  static Primitives P;
};

//Worklist engine declarations
class Constraint {
protected:
  WorkListEngine * engine;
public:
  virtual void resolve() const =0;
  virtual void print(raw_ostream &OS) const =0;
  virtual ~Constraint() {}
};

class WorkListEngine {
public:
  void solve();
  void add(Constraint*, bool isnew = true);
  //WorkListEngine is in charge of constraint deletion
  ~WorkListEngine();
  void printConstraints(raw_ostream &OS);
  std::map<const Constraint*, bool> getConstraints() { return constraints; }
  int getNumConstraints() { return constraints.size(); }
private:
  std::queue<const Constraint*> worklist;
  std::map<const Constraint*, bool> constraints;
};

// Constraint definitions
class LT : public Constraint {
  StrictRelations::Variable * const left, * const right;
public:
  LT(WorkListEngine* W, StrictRelations::Variable* L,
          StrictRelations::Variable* R) : left(L), right(R) { engine = W; };
  void resolve() const override;
  void print(raw_ostream &OS) const override;
};

class LE : public Constraint {
  StrictRelations::Variable * const left, * const right;
public:
  LE(WorkListEngine* W, StrictRelations::Variable* L,
          StrictRelations::Variable* R) : left(L), right(R) { engine = W; };
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
  std::set<StrictRelations::Variable*> operands;
public:
  PHI(WorkListEngine* W, StrictRelations::Variable* L,
                          std::set<StrictRelations::Variable*> Operands)
                          : left(L), operands(Operands) { engine = W; };
  void resolve() const override;
  void print(raw_ostream &OS) const override;
};

//Dependance graph declarations
class DepGraph {
public:
  void addVariable(StrictRelations::Variable*);
  // In constraints x = y is necessary to coalesce the nodes
  void coalesce (StrictRelations::Variable*, StrictRelations::Variable*);
  //In the case of a GEP
  void addEdge(StrictRelations::Variable*, StrictRelations::Variable*, Range,
                                                      const GetElementPtrInst*);

  // Forward declaration
  struct DepEdge;

  enum DepOp { Addition, Subtraction, Multiplication };

  struct DepNode {
    std::set<StrictRelations::Variable*> variables;
    std::set<DepEdge*> edges;
    std::set<DepEdge*> inedges;
  };

  struct DepEdge {
    DepNode* target;
    DepOp sign;
    DepOp operation;
    DepNode* operand;
    // GAMBIARRA!!
    Range range;
    const GetElementPtrInst* gep;
  };
private:

  std::map<StrictRelations::Variable*, DepNode*> nodes;

public:
  std::map<StrictRelations::Variable*, DepNode*>::iterator
                                            begin() { return nodes.begin(); }
  std::map<StrictRelations::Variable*, DepNode*>::iterator
                                            end() { return nodes.end(); }

};

}


#endif
