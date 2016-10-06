#define DEBUG_TYPE "sraa"
#include "StrictRelationsAliasAnalysis.h"

#include <utility>
#include <ctime>
#include <set>
#include <queue>

#include "llvm/Pass.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/User.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/PassAnalysisSupport.h"
//#include "../RangeAnalysis/RangeAnalysis.h" // Line not required

using namespace llvm;

extern unsigned MAX_BIT_INT;
extern APInt Min;
extern APInt Max;
extern APInt Zero;

Primitives StrictRelations::P;


STATISTIC(NumVariablesConst, "Number of variables in constraints");
STATISTIC(NumConstraints, "Number of constraints");
STATISTIC(NumResolve, "Number of resolve operations");
STATISTIC(NumNodes, "Number of dep graph nodes");
STATISTIC(NumEdges, "Number of dep graph edges");
STATISTIC(NumQueries, "Number of alias queries received");
STATISTIC(NumNoAlias, "Number of NoAlias answers");
STATISTIC(NumNoAlias1, "Number of NoAlias answers in test 1");
STATISTIC(NumNoAlias2, "Number of NoAlias answers in test 2");
STATISTIC(NumNoAlias3, "Number of NoAlias answers in test 3");

// Register this pass...
char StrictRelations::ID = 0;
static RegisterPass<StrictRelations> X("sraa",
                        "Strict relations alias analysis", false, false);
static RegisterAnalysisGroup<AliasAnalysis> E(X);

////////////////////////////////////////////////////////////////////////////////
// Primitives class implementation
//Returns the sum of previous elements of vector
int Primitives::getSumBehind(std::vector<int> v, unsigned int i) {
  int s = 0;
  if(i > v.size())
    i = v.size();
  for(int j = i-1; j >= 0; j--)
    s += v[j];
  return s;
}

//Returns the type of the ith element inside type
Type* Primitives::getTypeInside(Type* type, int i) {
  if(type->isPointerTy())
    return type->getPointerElementType();
  else if(type->isArrayTy())
    return type->getArrayElementType();
  else if(type->isStructTy())
    return type->getStructElementType(i);
  else if(type->isVectorTy())
    return type->getVectorElementType();
  else
    return NULL; 
}

//Returns the number of primitive elements of type
int Primitives::getNumPrimitives(Type* type) {
  //Verifies if this number of primitives was calculated already
  for(unsigned int i = 0; i < NumPrimitives.size(); i++)
    if(NumPrimitives[i]->type == type)
      return NumPrimitives[i]->num;
  
  //if not
  int np;
  if(type->isArrayTy()) {
    int num = type->getArrayNumElements();
    Type* arrtype = type->getArrayElementType();
    int arrtypenum = getNumPrimitives(arrtype); 
    np = num * arrtypenum;
  } else if(type->isStructTy()) {
    int num = type->getStructNumElements();
    np = 0;
    for(int i = 0; i < num; i++) {
      Type* structelemtype = type->getStructElementType(i);
      np += getNumPrimitives(structelemtype);
    }
  } else if(type->isVectorTy()) {
    int num = type->getVectorNumElements();
    Type* arrtype = type->getVectorElementType();
    int arrtypenum = getNumPrimitives(arrtype); 
    np = num * arrtypenum;
  } else {
    np = type->getPrimitiveSizeInBits();
    ///The type is not any one of the above or a primitive type
    // TODO: validate
    if (np == 0) np = 1;
    //assert(np > 0 && "Unrecognized type");
  }
  
  NumPrimitives.insert(NumPrimitives.end(), new NumPrimitive(type, np));
  return np;
}

//Returns a vector with the primitive layout of type
std::vector<int> Primitives::getPrimitiveLayout(Type* type) {
  //Verifies if this layout was calculated already
  for(unsigned int i = 0; i < PrimitiveLayouts.size(); i++)
    if(PrimitiveLayouts[i]->type == type)
      return PrimitiveLayouts[i]->layout;
  
  //if not
    
  if(type->isArrayTy()) {
    int num = type->getArrayNumElements();
    std::vector<int> pm (num);
    Type* arrtype = type->getArrayElementType();
    int arrtypenum = getNumPrimitives(arrtype); 
    for(int i = 0; i < num; i++)
      pm[i] = arrtypenum;
    PrimitiveLayouts.insert(PrimitiveLayouts.end(), 
      new PrimitiveLayout(type, pm));
    return pm;
  } else if(type->isStructTy()) {
    int num = type->getStructNumElements();
    std::vector<int> pm (num);
    for(int i = 0; i < num; i++) {
      Type* structelemtype = type->getStructElementType(i);
      pm[i] = getNumPrimitives(structelemtype);
    }
    PrimitiveLayouts.insert(PrimitiveLayouts.end(), 
      new PrimitiveLayout(type, pm));
    return pm;
  } else if(type->isVectorTy()) {
    int num = type->getVectorNumElements();
    std::vector<int> pm (num); 
    Type* arrtype = type->getVectorElementType();
    int arrtypenum = getNumPrimitives(arrtype); 
    for(int i = 0; i < num; i++)
      pm[i] = arrtypenum;
    PrimitiveLayouts.insert(PrimitiveLayouts.end(), 
      new PrimitiveLayout(type, pm));
    return pm;
  } else {
    std::vector<int> pm (1);
    pm[0] = 1;
    PrimitiveLayouts.insert(PrimitiveLayouts.end(), 
      new PrimitiveLayout(type, pm));
    return pm;
  }
}

////////////////////////////////////////////////////////////////////////////////
// StrictRelations definitions
StrictRelations::~StrictRelations() {
  phases += test1 + test2 + test3;
  errs() << "------------------------------------------\n";
  errs() << "                Times                     \n";
  errs() << "------------------------------------------\n";
  errs() << "Total time: " << phases << "\n";
  errs() << "Constraint collection time: " << phase1 << "\n";
  errs() << "Dependence graph time: " << phase2 << "\n";
  errs() << "Worklist time: " << phase3 << "\n";
  errs() << "Test 1 time: " << test1 << "\n";
  errs() << "Test 2 time: " << test2 << "\n";
  errs() << "Test 3 time: " << test3 << "\n";
  errs() << "------------------------------------------\n";
}

void StrictRelations::getAnalysisUsage(AnalysisUsage &AU) const {
  AliasAnalysis::getAnalysisUsage(AU);
  AU.addRequired<InterProceduralRA<Cousot> >();
  AU.setPreservesAll();
}

// Compares Values
StrictRelations::CompareResult StrictRelations::compareValues(const Value* V1,
                                                              const Value* V2) {
  if(variables.count(V1) and variables.count(V2)){
    if(variables[V1]->GT.count(variables[V2]))
      return L;
    else if(variables[V1]->LT.count(variables[V2]))
      return G;
  }
  Range r1, r2;

  if(V1 == NULL) r1 = Range(Zero, Zero);
  else r1 = RA->getRange(V1);

  if(V2 == NULL) r2 = Range(Zero, Zero);
  else r2 = RA->getRange(V2);

  if(r1.getLower().eq(r2.getLower()) and r1.getUpper().eq(r2.getUpper()))
    return E;
  else if(r1.getUpper().slt(r2.getLower()))
    return L;
  else if(r2.getUpper().slt(r1.getLower()))
    return G;
  
  return N;
}

// Compares GEPs by comparing pairs of operands
bool StrictRelations::disjointGEPs( const GetElementPtrInst* G1,
                                    const GetElementPtrInst* G2) {
  //return N;
  CompareResult r = E;
  auto i1 = G1->idx_begin();
  auto i2 = G2->idx_begin();
  auto ie1 = G1->idx_end();
  auto ie2 = G2->idx_end();
  while((i1 != ie1) or (i2 != ie2)) {
    const Value *v1, *v2;
    if(i1 == ie1) v1 = NULL;
    else v1 = *i1;

    if(i2 == ie2) v2 = NULL;
    else v2 = *i2;
    CompareResult c = compareValues(v1, v2);
    if(c == L) {
      if(r == L or r == E) r = L;
      else r = N;
    }
    else if(c == G) {
      if(r == G or r == E) r = G;
      else r = N;
    } else if(c == N) {
      return N;
    }
        
    if(i1 != ie1) i1++;
    if(i2 != ie2) i2++;
  }
  
  if(r == L or r == G) return true;
  else return false;
}

bool diff(Range r1, Range r2){
  if(r1.getLower().sgt(r2.getUpper())) return true;
  else if(r2.getLower().sgt(r1.getUpper())) return true;
  else return false;
}

AliasResult 
StrictRelations::alias(const MemoryLocation &LocA, const MemoryLocation &LocB) {
  NumQueries++;
  const Value *p1, *p2;
  p1 = LocA.Ptr;
  p2 = LocB.Ptr;
  if(nodes[p1]->mustalias == nodes[p2]->mustalias) return MustAlias;
  
  bool t1 = aliastest1(p1, p2);
  bool t2 = aliastest2(p1, p2);
  bool t3 = aliastest3(p1, p2);
  
  if(t1 or t2 or t3){ NumNoAlias++; return NoAlias;}
  else return AliasAnalysis::alias(LocA, LocB);
  
  AliasAnalysis::alias(LocA, LocB);   
}

bool StrictRelations::aliastest1(const Value* p1, const Value* p2) {
  clock_t t;
  t = clock();
  
  if(nodes.count(p1) and nodes.count(p2)) {
    DepNode* dp1 = nodes[p1];
    DepNode* dp2 = nodes[p2];
    
    // Local tree verification
    if(dp1->local_root == dp2->local_root) {
      int index = -1;
      DepNode* ancestor = NULL;
      for(auto i : dp1->path_to_root) {
        if(index > -1 and i.second.first > index) {
          continue;
        }
        else if(dp2->path_to_root.count(i.first)) {  
          if(index == -1 or i.second.first < index) {
           index = i.second.first;
           ancestor = i.first;
          }
        } 
      }

      if(diff(dp1->path_to_root[ancestor].second, dp2->path_to_root[ancestor].second)) {
        NumNoAlias1++;
        t = clock() - t;
        test1 += ((float)t)/CLOCKS_PER_SEC;
        return true;
      }
    }
  }
  t = clock() - t;
  test1 += ((float)t)/CLOCKS_PER_SEC;
  return false;
}

bool StrictRelations::aliastest2(const Value* p1, const Value* p2) {
  clock_t t;
  t = clock();
  
  if(!variables.count(p1)) variables[p1] = new StrictRelations::Variable(p1);
  if(!variables.count(p2)) variables[p2] = new StrictRelations::Variable(p2);
  Variable* v1 = variables[p1];
  Variable* v2 = variables[p2];
  if(v1->LT.count(v2) or v1->GT.count(v2)) {
    NumNoAlias2++;
    t = clock() - t;
    test2 += ((float)t)/CLOCKS_PER_SEC;
    return true;
  }
  if(const GetElementPtrInst* gep1 = dyn_cast<GetElementPtrInst>(p1))
    if(const GetElementPtrInst* gep2 = dyn_cast<GetElementPtrInst>(p2)) {
      if(nodes[gep1->getPointerOperand()]->mustalias == 
                                  nodes[gep2->getPointerOperand()]->mustalias) { 
        t = clock() - t;
        test2 += ((float)t)/CLOCKS_PER_SEC;
        return disjointGEPs(gep1, gep2);
      }
    }
  t = clock() - t;
  test2 += ((float)t)/CLOCKS_PER_SEC;
  return false;
}

bool StrictRelations::aliastest3(const Value* p1, const Value* p2) {
  clock_t t;
  t = clock();
  
  DepNode* dp1 = nodes[p1];
  DepNode* dp2 = nodes[p2];
  
  if(dp1->unk or dp2->unk) {
    t = clock() - t;
    test3 += ((float)t)/CLOCKS_PER_SEC;
    return false;
  }
  
  if(dp1->inedges.empty() and !dp1->arg and !dp1->alloca and !dp1->global) {
    t = clock() - t;
    test3 += ((float)t)/CLOCKS_PER_SEC;
    return false;
  }
  
  if(dp2->inedges.empty() and !dp2->arg and !dp2->alloca and !dp2->global) {
    t = clock() - t;
    test3 += ((float)t)/CLOCKS_PER_SEC;
    return false;
  }
  
  if(dp1->arg and !dp2->arg and !dp2->global) { 
    NumNoAlias3++;
    t = clock() - t;
    test3 += ((float)t)/CLOCKS_PER_SEC;
    return true;
  }
  
  if(dp2->arg and !dp1->arg and !dp1->global) {
    NumNoAlias3++;
    t = clock() - t;
    test3 += ((float)t)/CLOCKS_PER_SEC;
    return true;
  }
  
  if(dp1->locs.empty() or dp2->locs.empty()) { 
    t = clock() - t;
    test3 += ((float)t)/CLOCKS_PER_SEC;
    return false;
  }
  
  for(auto i : dp1->locs)
    if(dp2->locs.count(i)) {
      t = clock() - t;
      test3 += ((float)t)/CLOCKS_PER_SEC;
      return false;
    }
  
  NumNoAlias3++;
  t = clock() - t;
  test3 += ((float)t)/CLOCKS_PER_SEC;
  return true;  
}

bool StrictRelations::runOnModule(Module &M) {
  InitializeAliasAnalysis(this, &M.getDataLayout());
  RA = &getAnalysis<InterProceduralRACousot>();
  wle = new WorkListEngine();
  global_variable_translator = (void*) 
                                new BitVectorPositionTranslator<Variable*>();
  test1 = 0; test2 = 0; test3 = 0;
  clock_t t;
  t = clock();
  
  DEBUG_WITH_TYPE("phases", errs() << "Collecting constraints.\n");  
  collectConstraintsFromModule(M);
  NumVariablesConst = variables.size();
  t = clock() - t;
  phase1 = ((float)t)/CLOCKS_PER_SEC;
  
  DEBUG_WITH_TYPE("phases", errs() << "Building dependence graph.\n");  
  buildDepGraph(M);
  collectTypes();
  propagateTypes();
  for(auto i :nodes) i.second->getPathToRoot();
  t = clock() - t;
  phase2 = ((float)t)/CLOCKS_PER_SEC;
  
  DEBUG_WITH_TYPE("worklist", wle->printConstraints(errs()));
  DEBUG_WITH_TYPE("phases", errs() << "Running WorkList engine.\n");  
  wle->solve();
  t = clock() - t;
  phase3 = ((float)t)/CLOCKS_PER_SEC;

  //build LT graph
  buildTGraph(getResult(), errs());
  //generate dot file
  toDot("LT",errs());
  
  DEBUG_WITH_TYPE("phases", errs() << "Finished.\n");
  phases = phase1 + phase2 + phase3;
  
  return false;
}

// This function processes the indexes of a GEP operation and returns
// the actual bitwise range of its offset;
Range StrictRelations::processGEP(const Value* Base, const Use* idx_begin,
const Use* idx_end){
  Range r;
  //Number of primitive elements
  Type* base_ptr_type = Base->getType();
  int base_ptr_num_primitive = 
    StrictRelations::P.getNumPrimitives
                                    (base_ptr_type->getPointerElementType());

  //parse first index
  Value* indx = idx_begin->get();

  if(ConstantInt* cint = dyn_cast<ConstantInt>(indx)) {
    int constant = cint->getSExtValue();
    //updating lower and higher ranges
    r.setLower(APInt(MAX_BIT_INT, base_ptr_num_primitive * constant));
    r.setUpper(APInt(MAX_BIT_INT, base_ptr_num_primitive * constant));
  } else {
    Range a = RA->getRange(indx);
    //updating lower and higher ranges
    if(a.getLower().eq(Min))
      r.setLower(Min);
    else
      r.setLower(APInt(MAX_BIT_INT, base_ptr_num_primitive) * a.getLower());
    if(a.getUpper().eq(Max))
      r.setUpper(Max);
    else
      r.setUpper(APInt(MAX_BIT_INT, base_ptr_num_primitive) * a.getUpper());
  }

  //parse sequential indexes
  int index = 0;
  for(int i = 1; (idx_begin + i) != idx_end; i++) {
    //Calculating Primitive Layout
    base_ptr_type = StrictRelations::P.getTypeInside(base_ptr_type, index);
    std::vector<int> base_ptr_primitive_layout = 
      StrictRelations::P.getPrimitiveLayout(base_ptr_type);

    Value* indx = (idx_begin + i)->get();
    if(ConstantInt* cint = dyn_cast<ConstantInt>(indx)) {
      int constant = cint->getSExtValue();

      APInt addons(MAX_BIT_INT,
        StrictRelations::P.getSumBehind(base_ptr_primitive_layout, constant));
      Range addon(addons, addons);
      r = r.add(addon);

      index = constant;
    } else {
      Range a = StrictRelations::RA->getRange(indx);

      r = r.add(
        Range(
          APInt(MAX_BIT_INT, StrictRelations::P.getSumBehind
                    (base_ptr_primitive_layout, a.getLower().getSExtValue())),
          APInt(MAX_BIT_INT, StrictRelations::P.getSumBehind
                    (base_ptr_primitive_layout, a.getUpper().getSExtValue()))
        )
      );
      
      index = 0;
    }
  }
  return r;
}

void StrictRelations::collectConstraintsFromModule(Module &M) {
  // Map that holds the comparisons anf sigmas
  // cmp -> leftside<truesigma, falsesigma> , rightside<truesigma, falsesigma>
  std::map<const CmpInst*, std::pair< std::pair<const Value*, const Value*>,
                              std::pair<const Value*, const Value*> > > sigmas;

// Going through the module collecting constraints and sigmas
  for (Module::iterator m = M.begin(), me = M.end(); m != me; ++m) {
    for (Function::iterator b = m->begin(), be = m->end(); b != be; ++b) {
      for (BasicBlock::iterator I = b->begin(), ie = b->end(); I != ie; ++I) {

        // Renaming variables. Including funcion from where var belongs.
        // Only needed to make rendered graph easier to undestand
        const void * instAddr = static_cast<const void*>(I);
        std::stringstream stream;
        stream << instAddr;
        if(I->hasName()) I->setName(I->getName() + ".F(" + m->getName() + ")"); 
        else if(isa<Constant>(I)) I->setName( Twine(stream.str()) + b->getName() + ".F(" + m->getName() + ")"); 
        

        if(!variables.count(I)) variables[I] = new StrictRelations::Variable(I);
        // Addition
        if (isa<llvm::BinaryOperator>(&(*I))
        && (&(*I))->getOpcode()==Instruction::Add) { 
          // a = x + y
          Value * op1 = I->getOperand(0);
          Value * op2 = I->getOperand(1);
          Range r1 = RA->getRange(op1);
          Range r2 = RA->getRange(op2);
          // Evaluating the first operand 
          if(r1.getLower().eq(Zero) and r1.getUpper().eq(Zero)) {
            // Case a = 0 + y then a = y
            if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
            Constraint* c = new REQ(wle, variables[I], variables[op2]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op2]->constraints.insert(c);
            wle->add(c);
          }
          else if (r1.getLower().sgt(Zero)) {
            // Case x > 0 then y < a
            if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
            Constraint* c = new LT(wle, variables[op2], variables[I]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op2]->constraints.insert(c);
            wle->add(c);
          }
          else if (r1.getLower().sge(Zero)) {
            // Case x >= 0 then y <= a
            if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
            Constraint* c = new LE(wle, variables[op2], variables[I]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op2]->constraints.insert(c);
            wle->add(c);
          }
          else if (r1.getUpper().slt(Zero)) {
            // Case x < 0 then a < y
            if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
            Constraint* c = new LT(wle, variables[I], variables[op2]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op2]->constraints.insert(c);
            wle->add(c);
          }
          else if (r1.getUpper().sle(Zero)) {
            // Case x <= 0 then a <= y
            if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
            Constraint* c = new LE(wle, variables[I], variables[op2]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op2]->constraints.insert(c);
            wle->add(c);
          }
                    
          // Evaluating the second operand 
          if(r2.getLower().eq(Zero) and r2.getUpper().eq(Zero)) {
            // Case a = x + 0 then a = x
            if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new REQ(wle, variables[I], variables[op1]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getLower().sgt(Zero)) {
            // Case y > 0 then x < a
            if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LT(wle, variables[op1], variables[I]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getLower().sge(Zero)) {
            // Case y >= 0 then x <= a
            if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LE(wle, variables[op1], variables[I]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getUpper().slt(Zero)) {
            // Case y < 0 then a < x
            if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LT(wle, variables[I], variables[op1]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getUpper().sle(Zero)) {
            // Case y <= 0 then a <= x
            if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LE(wle, variables[I], variables[op1]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          
        }
        // Subtraction
        else if (isa<llvm::BinaryOperator>(&(*I))
        && (&(*I))->getOpcode()==Instruction::Sub) {
          // a = x - y
          Value * op1 = I->getOperand(0);
          Value * op2 = I->getOperand(1);
          Range r1 = RA->getRange(op1);
          Range r2 = RA->getRange(op2);
          // Evaluating the first operand 
          if(r1.getLower().eq(Zero) and r1.getUpper().eq(Zero)) {
            // Case a = 0 - y
            if(r2.getLower().eq(Zero) and r2.getUpper().eq(Zero)){
              // Case a = 0 - 0 then a = y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new REQ(wle, variables[I], variables[op2]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sgt(Zero)) {
              // Case y > 0 then a < y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[I], variables[op2]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sge(Zero)) {
              // Case y >= 0 then a <= y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LE(wle, variables[I], variables[op2]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getUpper().slt(Zero)) {
              // Case y < 0 then y < a
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[op2], variables[I]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getUpper().sle(Zero)) {
              // Case y <= 0 then y <= a
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LE(wle, variables[op2], variables[I]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
          }
          else if (r1.getLower().sgt(Zero)) {
            // Case x > 0 
            if(r2.getLower().eq(Zero) and r2.getUpper().eq(Zero)){
              // Case a = (>0) - 0 then y < a
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[op2], variables[I]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sgt(Zero)) {
              // Case y > 0, a = (>0) - (>0) then nothing 
            }
            else if (r2.getLower().sge(Zero)) {
              // Case y >= 0, a = (>0) - (>=0)  then nothing
            }
            else if (r2.getUpper().slt(Zero)) {
              // Case y < 0, a = (>0) - (<0) then y < a
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[op2], variables[I]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getUpper().sle(Zero)) {
              // Case y <= 0, a = (>0) - (<=0) then y < a 
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[op2], variables[I]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
          }
          else if (r1.getLower().sge(Zero)) {
            // Case x >= 0 
            if(r2.getLower().eq(Zero) and r2.getUpper().eq(Zero)){
              // Case a = (>=0) - 0 then y <= a
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LE(wle, variables[op2], variables[I]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sgt(Zero)) {
              // Case y > 0, a = (>=0) - (>0) then nothing 
            }
            else if (r2.getLower().sge(Zero)) {
              // Case y >= 0, a = (>=0) - (>=0)  then nothing
            }
            else if (r2.getUpper().slt(Zero)) {
              // Case y < 0, a = (>=0) - (<0) then y < a
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[op2], variables[I]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getUpper().sle(Zero)) {
              // Case y <= 0, a = (>=0) - (<=0) then y <= a 
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LE(wle, variables[op2], variables[I]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
          }
          else if (r1.getUpper().slt(Zero)) {
            // Case x < 0 
            if(r2.getLower().eq(Zero) and r2.getUpper().eq(Zero)){
              // Case a = (<0) - 0 then a < y 
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[I], variables[op2]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sgt(Zero)) {
              // Case y > 0, a = (<0) - (>0) then  a < y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[I], variables[op2]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sge(Zero)) {
              // Case y >= 0, a = (<0) - (>=0)  then a < y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[I], variables[op2]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getUpper().slt(Zero)) {
              // Case y < 0, a = (<0) - (<0) then nothing
            }
            else if (r2.getUpper().sle(Zero)) {
              // Case y <= 0, a = (<0) - (<=0) then  nothing
            }
          }
          else if (r1.getUpper().sle(Zero)) {
            // Case x <= 0 
            if(r2.getLower().eq(Zero) and r2.getUpper().eq(Zero)){
              // Case a = (<=0) - 0 then a <= y 
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LE(wle, variables[I], variables[op2]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sgt(Zero)) {
              // Case y > 0, a = (<=0) - (>0) then  a < y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[I], variables[op2]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sge(Zero)) {
              // Case y >= 0, a = (<=0) - (>=0)  then a <= y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LE(wle, variables[I], variables[op2]);
              NumConstraints++;
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getUpper().slt(Zero)) {
              // Case y < 0, a = (<=0) - (<0) then nothing
            }
            else if (r2.getUpper().sle(Zero)) {
              // Case y <= 0, a = (<=0) - (<=0) then  nothing
            }
          }
          
          
          // Evaluating the second operand 
          if(r2.getLower().eq(Zero) and r2.getUpper().eq(Zero)) {
            // Case a = x - 0 then a = x
              if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new REQ(wle, variables[I], variables[op1]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getLower().sgt(Zero)) {
            // Case y > 0 then a < x
              if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LT(wle, variables[I], variables[op1]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getLower().sge(Zero)) {
            // Case y >= 0 then a <= x
              if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LE(wle, variables[I], variables[op1]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getUpper().slt(Zero)) {
            // Case y < 0 then x < a
              if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LT(wle, variables[op1], variables[I]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getUpper().sle(Zero)) {
            // Case y <= 0 then x <= a
              if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LE(wle, variables[op1], variables[I]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
        }
        // GEP Instruction
        else if (const GetElementPtrInst* p = dyn_cast<GetElementPtrInst>(I)) {
          // Getting base pointer
          const Value* base = p->getPointerOperand();
          // Geting bit range of offset
          Range r = processGEP (base, p->idx_begin(), p->idx_end());
          if(r.getLower().eq(Zero) and r.getUpper().eq(Zero)) {
            // Case p = b + 0 then p = b
            if(!variables.count(base)) variables[base] =
                                        new StrictRelations::Variable(base);
            Constraint* c = new REQ(wle, variables[I], variables[base]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[base]->constraints.insert(c);
            wle->add(c);
          }
          else if (r.getLower().sgt(Zero)) {
            // Case p = b + (>0) then b < p
            if(!variables.count(base)) variables[base] =
                                        new StrictRelations::Variable(base);
            Constraint* c = new LT(wle, variables[base], variables[I]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[base]->constraints.insert(c);
            wle->add(c);
          }
          else if (r.getLower().sge(Zero)) {
            // Case p = b + (>=0) then b <= p
            if(!variables.count(base)) variables[base] =
                                        new StrictRelations::Variable(base);
            Constraint* c = new LE(wle, variables[base], variables[I]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[base]->constraints.insert(c);
            wle->add(c);
          }
          else if (r.getUpper().slt(Zero)) {
            // Case p = b + (<0) then p < b
            if(!variables.count(base)) variables[base] =
                                        new StrictRelations::Variable(base);
            Constraint* c = new LT(wle, variables[I], variables[base]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[base]->constraints.insert(c);
            wle->add(c);
          }
          else if (r.getUpper().sle(Zero)) {
            // Case p = b + (<=0) then p <= b
            if(!variables.count(base)) variables[base] =
                                        new StrictRelations::Variable(base);
            Constraint* c = new LE(wle, variables[I], variables[base]);
            NumConstraints++;
            variables[I]->constraints.insert(c);
            variables[base]->constraints.insert(c);
            wle->add(c);
          }
        }
        // Sigma
        else if(isa<PHINode>(&(*I)) && (I->getNumOperands() == 1) ) {
          const PHINode* p = dyn_cast<PHINode>(I);
          
          const BasicBlock* cmpBB = p->getIncomingBlock(0);

          if(!isa<BranchInst>(cmpBB->getTerminator())) {
            errs() << "Error on evaluating sigma!\n";
            continue;
          }
          const BranchInst* br = dyn_cast<BranchInst>(cmpBB->getTerminator());
          // Getting weather true or false sigma 
          const BasicBlock* curBB = I->getParent();
          bool trueSigma = curBB == br->getSuccessor(0);

          if(!br->isConditional()) {
            errs() << "Error on evaluating sigma!\n";
            continue;
          } 
          const Value* cmpV = br->getCondition();

          if (!isa<CmpInst>(cmpV)){
            errs() << "Error on evaluating sigma!\n";
            continue;
          }
          // Getting comparison instruction
          const CmpInst* cmpInst = dyn_cast<CmpInst>(cmpV);
          // Getting side of predicate
          bool leftSide = p->getIncomingValue(0) == cmpInst->getOperand(0);
          // Adding to sigmas structures
          if(leftSide and trueSigma)
            sigmas[cmpInst].first.first = p;
          else if(leftSide and !trueSigma)
            sigmas[cmpInst].first.second = p;
          else if(!leftSide and trueSigma)
            sigmas[cmpInst].second.first = p;
          else if(!leftSide and !trueSigma)
            sigmas[cmpInst].second.second = p;

          // Adding eq constraint
          const Value* op = p->getIncomingValue(0);
          if(!variables.count(op)) variables[op] =
                                          new StrictRelations::Variable(op);
          Constraint* c = new EQ(wle, variables[I], variables[op]);

          NumConstraints++;
          variables[I]->constraints.insert(c);
          variables[op]->constraints.insert(c);
          wle->add(c);
        }
        // Phi function
        else if(const PHINode* p = dyn_cast<PHINode>(I)) {
          std::unordered_set<StrictRelations::Variable*> vset;
          for(int i = 0, e = p->getNumIncomingValues(); i < e; i++) {
            const Value* op = p->getIncomingValue(i);
            if(!variables.count(op)) variables[op] =
                                          new StrictRelations::Variable(op);
            vset.insert(variables.at(op));
          }
          Constraint* c = new PHI(wle, variables[I], vset);

          NumConstraints++;
          variables[I]->constraints.insert(c);
          for(auto i : vset)
            i->constraints.insert(c);
          wle->add(c);
        }
        // Bitcasts and such
        else if(isa<BitCastInst>(&(*I))
        || isa<SExtInst>(&(*I))
        || isa<ZExtInst>(&(*I))) {
          const Value* op = I->getOperand(0);
          if(!variables.count(op)) variables[op] =
                                          new StrictRelations::Variable(op);
          Constraint* c = new REQ(wle, variables[I], variables[op]);

          NumConstraints++;
          variables[I]->constraints.insert(c);
          variables[op]->constraints.insert(c);
          wle->add(c);
        }
      }
    }
  }

  // Transforming the sigmas map into constraints
  for (auto i : sigmas) {
    CmpInst::Predicate pred = i.first->getPredicate();

    // if one of the sigma pairs is missing
    if(i.second.first.first == NULL and i.second.second.first != NULL)
      i.second.first.first = i.first->getOperand(0);
    else if (i.second.first.second == NULL and i.second.second.second != NULL)
      i.second.first.second = i.first->getOperand(0);
    else if (i.second.second.first == NULL and i.second.first.first != NULL)
      i.second.second.first = i.first->getOperand(1);
    else if (i.second.second.second == NULL and i.second.first.second != NULL)
      i.second.second.second = i.first->getOperand(1);
    
    Constraint* c;
    if(pred == CmpInst::ICMP_UGT or pred == CmpInst::ICMP_SGT) {
      if(variables.count(i.second.second.first) and
         variables.count(i.second.first.first)) {
        c = new LT(wle, variables[i.second.second.first],
                                    variables[i.second.first.first]);

        NumConstraints++;
        variables[i.second.second.first]->constraints.insert(c);
        variables[i.second.first.first]->constraints.insert(c);
        wle->add(c);
      }
      if(variables.count(i.second.first.second) and
         variables.count(i.second.second.second)) {
        c = new LE(wle, variables[i.second.first.second],
                        variables[i.second.second.second]);

        NumConstraints++;
        variables[i.second.first.second]->constraints.insert(c);
        variables[i.second.second.second]->constraints.insert(c);
        wle->add(c);
      }
    }
    else if(pred == CmpInst::ICMP_UGE or pred == CmpInst::ICMP_SGE) {
      if(variables.count(i.second.second.first) and
         variables.count(i.second.first.first)) {
        c = new LE(wle, variables[i.second.second.first],
                                    variables[i.second.first.first]);

        NumConstraints++;
        variables[i.second.second.first]->constraints.insert(c);
        variables[i.second.first.first]->constraints.insert(c);
        wle->add(c);
      }
      if(variables.count(i.second.first.second) and
         variables.count(i.second.second.second)) {
        c = new LT(wle, variables[i.second.first.second],
                        variables[i.second.second.second]);

        NumConstraints++;
        variables[i.second.first.second]->constraints.insert(c);
        variables[i.second.second.second]->constraints.insert(c);
        wle->add(c);
      }
    }
    else if(pred == CmpInst::ICMP_ULT or pred == CmpInst::ICMP_SLT) {
      if(variables.count(i.second.first.first) and
         variables.count(i.second.second.first)) {
        c = new LT(wle, variables[i.second.first.first],
                                    variables[i.second.second.first]);
      
        NumConstraints++;
        variables[i.second.first.first]->constraints.insert(c);
        variables[i.second.second.first]->constraints.insert(c);
        wle->add(c);
      }
      if(variables.count(i.second.second.second) and
         variables.count(i.second.first.second)) {
        c = new LE(wle, variables[i.second.second.second],
                        variables[i.second.first.second]);

        NumConstraints++;
        variables[i.second.second.second]->constraints.insert(c);
        variables[i.second.first.second]->constraints.insert(c);
        wle->add(c);
      }
    }
    else if(pred == CmpInst::ICMP_ULE or pred == CmpInst::ICMP_SLE) {
      if(variables.count(i.second.first.first) and
         variables.count(i.second.second.first)) {
        c = new LE(wle, variables[i.second.first.first],
                                    variables[i.second.second.first]);

        NumConstraints++;
        variables[i.second.first.first]->constraints.insert(c);
        variables[i.second.second.first]->constraints.insert(c);
        wle->add(c);
      }
      if(variables.count(i.second.second.second) and
         variables.count(i.second.first.second)) {
        c = new LT(wle, variables[i.second.second.second],
                        variables[i.second.first.second]);

        NumConstraints++;
        variables[i.second.second.second]->constraints.insert(c);
        variables[i.second.first.second]->constraints.insert(c);
        wle->add(c);
      }
    }
    else if(pred == CmpInst::ICMP_EQ) {
      if(variables.count(i.second.first.first) and
         variables.count(i.second.second.first)) {
        c = new REQ(wle, variables[i.second.first.first],
                                    variables[i.second.second.first]);

        NumConstraints++;
        variables[i.second.first.first]->constraints.insert(c);
        variables[i.second.second.first]->constraints.insert(c);
        wle->add(c);
      }
    }
    else if(pred == CmpInst::ICMP_NE) {
      if(variables.count(i.second.first.second) and
         variables.count(i.second.second.second)) {
        c = new REQ(wle, variables[i.second.first.second],
                                    variables[i.second.second.second]);

        NumConstraints++;
        variables[i.second.first.second]->constraints.insert(c);
        variables[i.second.second.second]->constraints.insert(c);
        wle->add(c);
      }
    }
  }
}

void StrictRelations::DepNode::coalesce (StrictRelations::DepNode* other){
  if(mustalias == other->mustalias) return;
  std::unordered_set<DepNode*>* to_coalesce = other->mustalias;
  for(auto i : *to_coalesce) i->mustalias = mustalias;
  mustalias->insert(to_coalesce->begin(), to_coalesce->end());
  delete to_coalesce;           
}

void StrictRelations::buildDepGraph(Module &M){
  std::set<const Value*> pointers;
  /// Go through global variables to find arrays, structs and pointers
  for(auto i = M.global_begin(), e = M.global_end(); i != e; i++) {
    //Since all globals are pointers, all are inserted
    pointers.insert(i);
  }
  /// Go through all functions from the module
  for (auto F = M.begin(), Fe = M.end(); F != Fe; F++) {
    /// Go through parameters (add if they are pointers)
    for(auto i = F->arg_begin(), e = F->arg_end(); i != e; i++) {
      Type* const arg_type = i->getType();
      if(arg_type->isPointerTy()) {
        pointers.insert(i);
      }
    }
     /// Run through instructions from function
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      const Instruction* i = &(*I);
      const Type *type = i->getType();
      if(type->isPointerTy()){
        pointers.insert(i);
      }
      ///verify intruction operands
      for(auto oi = i->op_begin(), oe = i->op_end(); oi != oe; oi++) {
        const Value* oper = *oi;
        const Type *op_type = oper->getType();
        if(op_type->isPointerTy()){
		  pointers.insert(oper);
		} 
      }
    }
  }
  
  NumNodes = pointers.size();
  for(auto i : pointers){
    nodes[i] = new DepNode(i);
  }
  
  //Finding edges
  for(auto i : nodes) {
    if(const Argument* p = dyn_cast<Argument>(i.first)) {
      const Function* F = p->getParent();
      //Go through all the uses of the argument's function, the calls are
      // the addresses bases
      for(auto ui = F->user_begin(), ue = F->user_end(); ui != ue; ui++) {
        const User* u = *ui;
        if(const CallInst* caller = dyn_cast<CallInst>(u)) {
          int anum = caller->getNumArgOperands();
          int ano = p->getArgNo();
          if(ano <= anum) {
            const Value* base = caller->getArgOperand(ano);
            if(!nodes.count(base)) nodes[base] = new DepNode(base);
            DepNode::addEdge(i.second, nodes[base], Range(Zero,Zero));
            NumEdges++;
          } else {
            /// TODO: support standard values in cases where the argument
            /// has a standard value and does not appear in function call
            DEBUG_WITH_TYPE("errors",
              errs() << "!: ERROR (Not enough arguments):\n");
            DEBUG_WITH_TYPE("errors", errs() << *p << " " << ano << "\n");
            DEBUG_WITH_TYPE("errors", errs() << *u << "\n");
            i.second->unk = true;
            std::set<DepEdge*> to_remove;
            for(auto e : i.second->inedges) to_remove.insert(e);
            for(auto e : to_remove) DepEdge::deleteEdge(e);
           return;
          }
        }
      }	
	  }
    else if(const CallInst* p = dyn_cast<CallInst>(i.first)) {
	    Function* CF = p->getCalledFunction();
      if(CF) {
        if(strcmp( CF->getName().data(), "realloc") == 0)
        {
          /// realloc is connected with it's first argument
          const Value* base = p->getOperand(0);
          if(!nodes.count(base)) nodes[base] = new DepNode(base);
          DepNode::addEdge(i.second, nodes[base], Range(Zero,Zero));
          NumEdges++;
        } else {
          for (auto j = inst_begin(CF), e = inst_end(CF); j != e; j++)
            if(isa<const ReturnInst>(*j)) {
              /// create edge
              const Value* ret_ptr = ((ReturnInst*)&(*j))->getReturnValue();
              if(!nodes.count(ret_ptr)) nodes[ret_ptr] = new DepNode(ret_ptr);
              DepNode::addEdge(i.second, nodes[ret_ptr], Range(Zero,Zero));
              NumEdges++;
            }
        }
      }
	  } 
    else if(const GetElementPtrInst* p = dyn_cast<GetElementPtrInst>(i.first)) {
	    // Getting base pointer
      const Value* base = p->getPointerOperand();
      // Geting bit range of offset
      Range r = processGEP (base, p->idx_begin(), p->idx_end());
      
      if(!nodes.count(base)) nodes[base] = new DepNode(base);
      if(r == Range(Zero, Zero)) nodes[base]->coalesce(i.second);
      DepNode::addEdge(i.second, nodes[base], r);
      NumEdges++;
	  }
    else if(const BitCastInst* p = dyn_cast<BitCastInst>(i.first)) {
	    const Value* base = p->getOperand(0);
      if(!nodes.count(base)) nodes[base] = new DepNode(base);
      nodes[base]->coalesce(i.second);
      DepNode::addEdge(i.second, nodes[base], Range(Zero,Zero));
      NumEdges++;
	  }
    else if(const SExtInst* p = dyn_cast<SExtInst>(i.first)) {
	    const Value* base = p->getOperand(0);
      if(!nodes.count(base)) nodes[base] = new DepNode(base);
      nodes[base]->coalesce(i.second);
      DepNode::addEdge(i.second, nodes[base], Range(Zero,Zero));
      NumEdges++;
	  }
    else if(const ZExtInst* p = dyn_cast<ZExtInst>(i.first)) {
	    const Value* base = p->getOperand(0);
      if(!nodes.count(base)) nodes[base] = new DepNode(base);
      nodes[base]->coalesce(i.second);
      DepNode::addEdge(i.second, nodes[base], Range(Zero,Zero));
      NumEdges++;
	  }
    else if(const PHINode* p = dyn_cast<PHINode>(i.first)) {
	    for(unsigned int j = 0; j < p->getNumIncomingValues(); j++){
	      const Value* base = p->getIncomingValue(j);
	      if(!nodes.count(base)) nodes[base] = new DepNode(base);
        DepNode::addEdge(i.second, nodes[base], Range(Zero,Zero));
        NumEdges++;
	    }
	  }
    else if(const GEPOperator* p = dyn_cast<GEPOperator>(i.first)) {
	    // Getting base pointer
      const Value* base = p->getPointerOperand();
      // Geting bit range of offset
      Range r = processGEP (base, p->idx_begin(), p->idx_end());
      
      if(!nodes.count(base)) nodes[base] = new DepNode(base);
      DepNode::addEdge(i.second, nodes[base], r);
      NumEdges++;
	  }
    else if(const ConstantExpr* p = dyn_cast<ConstantExpr>(i.first)) {
	  const char* operation = p->getOpcodeName();
      if(strcmp(operation, "bitcast") == 0) {
        const Value* base = p->getOperand(0);
        if(!nodes.count(base)) nodes[base] = new DepNode(base);
        nodes[base]->coalesce(i.second);
        DepNode::addEdge(i.second, nodes[base], Range(Zero,Zero));
        NumEdges++;
      }
	  }
    
  }
    
}

void StrictRelations::collectTypes() {
  for(auto i : nodes) {
    if(isa<const Argument>(*(i.first))) {
      i.second->arg = true;
    }
    else if(isa<const GlobalVariable>(*(i.first))) {
      i.second->global = true;
      i.second->alloca = true;
    }
    else if(isa<const AllocaInst>(*(i.first))) {
      i.second->alloca = true;
    }
    else if(const CallInst* p = dyn_cast<CallInst>(i.first)) { 
        Function* CF = p->getCalledFunction();
        if(CF) {
          if(strcmp( CF->getName().data(), "malloc") == 0)
           i.second->alloca = true;
          else if(strcmp( CF->getName().data(), "calloc") == 0)
            i.second->alloca = true;
          else i.second->call = true;
        } else { 
          i.second->unk = true;
        }
    }
    else if(isa<const ConstantPointerNull>(*(i.first))) { 
      i.second->alloca = true;
    }
    else if(isa<const Function>(*(i.first))) { 
      i.second->alloca = true;
    }
    else if(const ConstantExpr* p = dyn_cast<ConstantExpr>(i.first)) { 
        const char* operation = p->getOpcodeName();
        if(strcmp(operation, "bitcast") != 0) 
          i.second->unk = true;
    }
  }  
}

void StrictRelations::propagateTypes(){
  std::set<DepNode*> args;
  std::set<DepNode*> globals;
  std::set<DepNode*> unks;
  std::set<DepNode*> allocas;
  for(auto i : nodes){
    if(i.second->arg) args.insert(i.second);  
    if(i.second->global) globals.insert(i.second); 
    if(i.second->unk) unks.insert(i.second);
    if(i.second->alloca) allocas.insert(i.second);  
  }
  std::queue<DepNode*>to_visit;
  std::unordered_set<DepNode*>visited;
  //Propagating args
  propagateArgs(args);
  //Propagating globals
  propagateGlobals(globals);
  //Propagating unks
  propagateUnks(unks); 
  //Propagating allocas
  for(auto i : allocas) {
    propagateAlloca(i);
  }
}

void StrictRelations::propagateArgs(std::set<DepNode*> &args) {
  std::queue<DepNode*>to_visit;
  std::unordered_set<DepNode*>visited;
  
  for(auto i : args) to_visit.push(i);
  while(!(to_visit.empty())){
    DepNode* current = to_visit.front();
    to_visit.pop();
    visited.insert(current);
    if(!(current->call)){
      current->arg = true;
      for(auto i : current->outedges){
        if(!(visited.count(i->in))){
         to_visit.push(i->in);
        }
      }
    }
  }
}

void StrictRelations::propagateGlobals(std::set<DepNode*> &globals) {
  std::queue<DepNode*>to_visit;
  std::unordered_set<DepNode*>visited;
  
  for(auto i : globals) to_visit.push(i);
  while(!(to_visit.empty())){
    DepNode* current = to_visit.front();
    to_visit.pop();
    current->global = true;
    visited.insert(current);
    
    for(auto i : current->outedges){
      if(!(visited.count(i->in))){
	     to_visit.push(i->in);
	    }
    }
  }
}

void StrictRelations::propagateUnks(std::set<DepNode*> &unks) {
  std::queue<DepNode*>to_visit;
  std::unordered_set<DepNode*>visited;
  
  for(auto i : unks) to_visit.push(i);
  while(!(to_visit.empty())){
    DepNode* current = to_visit.front();
    to_visit.pop();
    current->unk = true;
    visited.insert(current);
    
    for(auto i : current->outedges){
      if(!(visited.count(i->in))){
	     to_visit.push(i->in);
	    }
    }
  }
}

void StrictRelations::propagateAlloca(DepNode* alloca) {
  std::queue<DepNode*>to_visit;
  std::unordered_set<DepNode*>visited;
  
  to_visit.push(alloca);
  const Value* a = alloca->v;
  while(!(to_visit.empty())){
    DepNode* current = to_visit.front();
    to_visit.pop();
    current->locs.insert(a);
    visited.insert(current);
    
    for(auto i : current->outedges){
      if(!(visited.count(i->in))){
       to_visit.push(i->in);
      }
    }
  }
}

void StrictRelations::DepNode::getPathToRoot() {
  DepNode* current = this;
  int index = 0;
  Range offset = Range(Zero,Zero);
  while(true) {
    path_to_root[current] = std::pair<int, Range>(index, offset);
    if(current->inedges.size() == 1) {
      DepEdge* addr = *(current->inedges.begin());
      current = addr->out;
      if(path_to_root.count(current)) {
        //This means that the local tree is actually a lonely loop
      	// so the local tree's root will be the pointer with the highest address
      	DepNode* root = NULL;
      	for(auto i : path_to_root){
      		if(root < i.first) root = i.first;
      	}
      	local_root = root;
      	break;
      }
      index++;
      offset = offset.add(addr->range);
    } else {
      local_root = current;
      break;
    }
  }
}

////////////////////////////////////////////////////////////////////////////////
// WorkListEngine definitions

void WorkListEngine::solve() {
  for(auto i : constraints) push(i.first);
  
  while(!worklist.empty()) {
    const Constraint* c = worklist.front();
    worklist.pop();
    constraints[c] = false;
    DEBUG_WITH_TYPE("worklist", errs() << "=> ");
    DEBUG_WITH_TYPE("worklist", c->print(errs()));
    c->resolve();
    NumResolve++;
  }
}

void WorkListEngine::add(const Constraint* C) {
  if(!constraints.count(C))
    constraints[C] = false;
}

WorkListEngine::~WorkListEngine() {
  for(auto i : constraints)
    delete i.first;
}

void WorkListEngine::printConstraints(raw_ostream &OS) {
  OS << "Constraints:\n";
  OS << "-------------------------------------------------\n";
  for(auto i : constraints)
    i.first->print(OS);
  OS << "-------------------------------------------------\n";
}

void WorkListEngine::push(const Constraint* C) {
  if(constraints.count(C) and !constraints.at(C)) {
    worklist.push(C);
    constraints[C] = true;
  }
}
////////////////////////////////////////////////////////////////////////////////
// Constraints definitions

// SA(x) U= {y} && SA(y) U {x} // REM:
void insertSA(StrictRelations::Variable* x,
                               StrictRelations::Variable* y,
                               StrictRelations::VariableSet &changed) {
  if(!x->SA.count(y) and x != y) {
    x->SA.insert(y);
    changed.insert(x);
    if(!y->SA.count(x)) {
      y->SA.insert(x);
      changed.insert(y);
    }
  }
}


// LT(x) U= {y}
void insertLT(StrictRelations::Variable* x,
                               StrictRelations::Variable* y,
                               StrictRelations::VariableSet &changed) {
  if(!x->LT.count(y) and x != y and !x->SA.count(y)) { //Added check for SA set
    x->LT.insert(y);
    changed.insert(x);
    if(!y->GT.count(x)) {
      y->GT.insert(x);
      changed.insert(y);
    }
  }
}

// GT(x) U= {y}
void insertGT(StrictRelations::Variable* x,
                               StrictRelations::Variable* y,
                               StrictRelations::VariableSet &changed) {
  if(!x->GT.count(y) and x != y and !x->SA.count(y)) { //Added check for SA set
    x->GT.insert(y);
    changed.insert(x);
    if(!y->LT.count(x)) {
      y->LT.insert(x);
      changed.insert(y);
    }
  }
}

// SA(x) U= SA(y) //REM:
void unionSA(StrictRelations::Variable* x,
                               StrictRelations::Variable* y,
                               StrictRelations::VariableSet &changed) {
  for(auto i : y->SA) {
    insertSA(x, i, changed);
  }
}


// LT(x) U= LT(y)
void unionLT(StrictRelations::Variable* x,
                               StrictRelations::Variable* y,
                               StrictRelations::VariableSet &changed) {
  for(auto i : y->LT) {
    insertLT(x, i, changed);
  }
}

// GT(x) U= GT(y)
void unionGT(StrictRelations::Variable* x,
                               StrictRelations::Variable* y,
                               StrictRelations::VariableSet &changed) {
  for(auto i : y->GT) {
    insertGT(x, i, changed);
  }
}

StrictRelations::VariableSet intersect
                          (StrictRelations::VariableSet &s1,
                           StrictRelations::VariableSet &s2) {
  StrictRelations::VariableSet r;
  for(auto i : s1) if(s2.count(i)) r.insert(i);
  return r;
}

void LT::resolve() const {
  // x < y
  StrictRelations::VariableSet changed;
  
  // LT(y) U= LT(x) U {x}
  unionLT(right, left, changed);
  insertLT(right, left, changed);

  // GT(x) U= GT(y) U {y}
  unionGT(left, right, changed);
  insertGT(left, right, changed);

  // Adding back constraints from changed abstract values
  for(auto c : changed){
    DEBUG_WITH_TYPE("worklist", c->printStrictRelations(errs()));
    for(auto i : c->constraints)
      if(i != this) engine->push(i);
  }
}  
void LE::resolve() const { 
  // x <= y
  StrictRelations::VariableSet changed;
  
  // LT(y) U= LT(x)
    unionLT(right, left, changed);
  // GT(x) U= GT(y)
    unionGT(left, right, changed);
  // Adding back constraints from changed abstract values
  for(auto c : changed){
    DEBUG_WITH_TYPE("worklist", c->printStrictRelations(errs()));
    for(auto i : c->constraints)
      if(i != this) engine->push(i);
  }
}
void REQ::resolve() const { 
  // x = y
  StrictRelations::VariableSet changed;
  // LT(x) U= LT(y)
    unionLT(left, right, changed);
  // LT(y) U= LT(x)
    unionLT(right, left, changed);
  // GT(x) U= GT(y)
    unionGT(left, right, changed);
  // GT(y) U= GT(x)
    unionGT(right, left, changed);
    // SA(x) U= SA(y) and SA(y) U= SA(x) // REM:
    unionSA(right, left, changed);
    unionSA(left, right, changed);

  // Adding back constraints from changed abstract values
  for(auto c : changed) {
    DEBUG_WITH_TYPE("worklist", c->printStrictRelations(errs()));
    for(auto i : c->constraints)
      if(i != this) engine->push(i);
  }
}

void EQ::resolve() const { 
  // x = y
  StrictRelations::VariableSet changed;
  // LT(x) U= LT(y)
    unionLT(left, right, changed);
  // GT(x) U= GT(y)
    unionGT(left, right, changed);
  // SA(x) U= SA(y) // REM:
    unionSA(left, right, changed);
  // Adding back constraints from changed abstract values
  for(auto c : changed) {
    DEBUG_WITH_TYPE("worklist", c->printStrictRelations(errs()));
    for(auto i : c->constraints)
      if(i != this) engine->push(i);
  }
  
}

void PHI::resolve() const { 
  // x = I( xi )
  StrictRelations::VariableSet changed;
  // Growth checks
  bool gu = false, gd = false;
  for (auto i : operands) if (i->LT.count(left)) { gu = true; break; }
  for (auto i : operands) if (i->GT.count(left)) { gd = true; break; }
  
  StrictRelations::VariableSet ULT, UGT, USA;
  
  // If it can only grow up
  if(gu and !gd) {
    // LT(x) U= I( LT(xj) ), where x !E LT(xj)
    // Intersection part
    auto i = operands.begin();
    //Note: I think would be better to invert this do while to a
    //while loop and insert the if condition to end() inside it
    if(i != operands.end()) do {
      ULT = (*i)->LT;
      i++;
    } while (ULT.count(left) and i != operands.end());
    
    for (auto e = operands.end(); i != e; i++)
      if(!(*i)->LT.count(left)) ULT = intersect(ULT, (*i)->LT);
     
  } else {
    // LT(x) U= I( LT(xi) )
    auto i = operands.begin();
    if(i != operands.end()) {
      ULT = (*i)->LT;
      i++;
      for (auto e = operands.end(); i != e; i++) ULT = intersect(ULT, (*i)->LT);
    }
  }
  
  // If it can only grow down
  if(!gu and gd) {
    // GT(x) U= I( GT(xj) ), where x !E GT(xj)
    // Intersection part
    auto i = operands.begin();
    if(i != operands.end()) do {
    UGT = (*i)->GT;
    i++;
    } while (UGT.count(left) and i != operands.end());
    
    for (auto e = operands.end(); i != e; i++)
      if(!(*i)->GT.count(left)) UGT = intersect(UGT, (*i)->GT);
    
  } else {
    // GT(x) U= I( GT(xi) )
    auto i = operands.begin();
    if(i != operands.end()) {
      UGT = (*i)->GT;
      i++;
      for (auto e = operands.end(); i != e; i++) UGT = intersect(UGT, (*i)->GT);
    }
  }

  
  // SA(x) U= I( SA(xi) )
  auto i = operands.begin();
  if(i != operands.end()) {
    USA = (*i)->SA;
    i++;
    for (auto e = operands.end(); i != e; i++) 
      USA = intersect(USA, (*i)->SA);
  }

  // Remove left from ULT and UGT
  ULT.erase(left);
  UGT.erase(left);

  // Remove vars from SA set of left from ULT and UGL
  for (auto i : left->SA){
    ULT.erase(i);
    UGT.erase(i);
  }
  // U= part
    for(auto i : ULT) insertLT(left, i, changed);
    for(auto i : UGT) insertGT(left, i, changed);
    for(auto i : USA) insertSA(left, i, changed);
  
  // Adding back constraints from changed abstract values
  for(auto c : changed){
    DEBUG_WITH_TYPE("worklist", c->printStrictRelations(errs()));
    for(auto i : c->constraints)
      if(i != this) engine->push(i);
  }
}

void LT::print(raw_ostream &OS) const {
  if(left->v->getValueName() == NULL) OS << *(left->v);
  else OS << left->v->getName();
  OS << " < ";
  if(right->v->getValueName() == NULL) OS << *(right->v);
  else OS << right->v->getName();
  OS << "\n";
}
void LE::print(raw_ostream &OS) const {
  if(left->v->getValueName() == NULL) OS << *(left->v);
  else OS << left->v->getName();
  OS << " <= ";
  if(right->v->getValueName() == NULL) OS << *(right->v);
  else OS << right->v->getName();
  OS << "\n";
}
void REQ::print(raw_ostream &OS) const {
  if(left->v->getValueName() == NULL) OS << *(left->v);
  else OS << left->v->getName();
  OS << " == ";
  if(right->v->getValueName() == NULL) OS << *(right->v);
  else OS << right->v->getName();
  OS << "\n";
}
void EQ::print(raw_ostream &OS) const {
  if(left->v->getValueName() == NULL) OS << *(left->v);
  else OS << left->v->getName();
  OS << " = ";
  if(right->v->getValueName() == NULL) OS << *(right->v);
  else OS << right->v->getName();
  OS << "\n";
}
void PHI::print(raw_ostream &OS) const {
  if(left->v->getValueName() == NULL) OS << *(left->v);
  else OS << left->v->getName();
  OS << " = o| ";
  for(auto i : operands) {
    if(i->v->getValueName() == NULL) OS << *(i->v);
    else OS << i->v->getName();
    OS << "; ";
  }
  OS << "\n";
}

void StrictRelations::Variable::printStrictRelations(raw_ostream &OS) {
  if(v->getValueName() == NULL) OS << *(v);
    else OS << v->getName();
    OS << "\nLT: {";
    if(LT.empty()) OS << "E";
    for(auto j : LT) {
      if(j->v->getValueName() == NULL) OS << *(j->v);
      else OS << j->v->getName();
      OS << "; ";
    }
    OS << "}\nGT: {";
    if(GT.empty()) OS << "E";
    for(auto j : GT) {
      if(j->v->getValueName() == NULL) OS << *(j->v);
      else OS << j->v->getName();
      OS << "; ";
    }
    OS << "}\n";
}




/*

 TNode Implementation

*/

 
StrictRelations::TNode::TNode(StrictRelations::Variable* obj) {
  variable = obj;
}

 
StrictRelations::TNode::~TNode() {
  for (std::unordered_set<TNode*>::iterator pred = greaterThanSet.begin(); pred
          != greaterThanSet.end(); pred++) {
    (*pred)->lessThanSet.erase(this);
  }
  for (std::unordered_set<TNode*>::iterator succ = lessThanSet.begin(); succ
          != lessThanSet.end(); succ++) {
    (*succ)->greaterThanSet.erase(this);
  }
  lessThanSet.clear();
  greaterThanSet.clear();
}

 
std::unordered_set<StrictRelations::TNode*> StrictRelations::TNode::getSetLT() {
  return lessThanSet;
}
 
std::unordered_set<StrictRelations::TNode*> StrictRelations::TNode::getSetGT() {
  return greaterThanSet;
}

/* obj this is less than dst
the lessThanSet store all variables less than me
this will be included in the lessThanSet of dst
*/
void StrictRelations::TNode::addEdgeTo(StrictRelations::TNode* dst) { 
  dst->lessThanSet.insert(this);
  this->greaterThanSet.insert(dst);
}
 
bool StrictRelations::TNode::hasLT(StrictRelations::TNode* succ) {
  return lessThanSet.count(succ) > 0;
}
 
bool StrictRelations::TNode::hasGT(StrictRelations::TNode* pred) {
        return greaterThanSet.count(pred) > 0;
}




StrictRelations::TNode* StrictRelations::addNode(StrictRelations::Variable* variable) {
  TNode* node = findNode(tNodesMap, variable);
  if (!node) {
    node = new TNode(variable);
    tNodes.insert(node);
    //nodeMap[variable] = node;
    tNodesMap[variable->v] = node;
  }
  return node;
}



//Return the pointer to the node related to the element.
//Return NULL if the element is not inside the map.

StrictRelations::TNode* StrictRelations::findNode( std::unordered_map<const Value*,
                          TNode*> tNodesMap, StrictRelations::Variable* element) {
  if (tNodesMap.count(element->v))
    return tNodesMap[element->v];

  return NULL;
}


StrictRelations::TNode* StrictRelations::findNode(std::set<TNode*> tNodes, 
                                          StrictRelations::TNode* node) {
    if (tNodes.count(node))
      return node;

    return NULL;
}


void StrictRelations::buildTGraph(std::unordered_map<const Value*, 
                    StrictRelations::Variable*> variables, raw_ostream &OS){
  for(auto i : variables) {
    TNode* to = addNode(i.second);
    for(auto j : i.second->LT) {
      if(i.second->GT.count(j))
        OS << "\n=== LOOP:" << to->getName() << " - " << j->v->getName() << "\n"; 
      TNode* from = addNode(j);
      from->addEdgeTo(to);
    }
  }
}



void StrictRelations::toDot(std::string outName, raw_ostream &OS){
 // unsigned int numVertices = 2;
  //unsigned int numEdgesLT = 0;
 // unsigned int numEdgesGT = 0;
  //bool unused = false;
  std::map<const Value*, int> constantName;
  std::string name, name2;
  int cId = 0;
  dotFile* dot = new dotFile(outName);


  for (std::set<TNode*>::iterator node = tNodes.begin(), end = tNodes.end(); node
                        != end; node++) {   
    const Value *val = (*node)->getValue();    

    if(val->getValueName() == NULL){ // OS << "\n\n====>>>" << *(i.first) << "<<======\n";
      if(isa<Instruction>(val)) { 
        const Instruction* tst = dyn_cast<Instruction>(val);
        name = dot->recreateName(tst);      
                //OS << "INST(" << *(i.first) << ") OPCODE(" << tst->getOpcodeName()  << ") \n ";
      }else{
        if(constantName.count(val)){
          name = "Instruction ID: (";
          name += std::to_string(constantName[val]);
          name += ") ";
        }else{
          cId++;
          constantName[val] = cId;
          name = "Instruction ID: (";
          name += std::to_string(cId);
          name += ") ";
        }
      }
      /*}else if(const ConstantInt* CI = dyn_cast<ConstantInt>(val)){
        name = "ConstInt: " + CI->getValue().toString(10, true); //"CONSTANT";  
      }else if(const Constant* C = dyn_cast<Constant>(val)){    
        name = "Const: " + C->getName().str();
      }else{
                //OS << "VALUE(" << *(i.first) << ")\n";
        name = "OTHER";
      }*/
      dot->insertLine(name);
    }else{
      name = val->getName().str();
      dot->insertLine(name);
    }


    std::unordered_set<TNode*> SET = (*node)->getSetGT();
    for (std::unordered_set<TNode*>::iterator node2 = SET.begin(), end2 = SET.end(); node2
                        != end2; node2++) {
      const Value *valTo = (*node2)->getValue();
      //OS << (*node2)->getName() << " - ";
      if(valTo->getValueName() == NULL){
        if(isa<Instruction>(valTo)) { 
          const Instruction* tst2 = dyn_cast<Instruction>(valTo);
          name2 = dot->recreateName(tst2);
             //OS << "INST(" << *(i.first) << ") OPCODE(" << tst->getOpcodeName()  << ") \n ";
        }else{
          if(constantName.count(val)){
            name2 = "Instruction ID: (";
            name2 += std::to_string(constantName[valTo]);
            name2 += ") ";
          }else{
            cId++;
            constantName[valTo] = cId;
            name2 = "Instruction ID: (";
            name2 += std::to_string(cId);
            name2 += ") ";
          }
        }
        /*}else if(const ConstantInt* CI = dyn_cast<ConstantInt>(valTo) ){
          name2 = "ConstInt: " + CI->getValue().toString(10, true); //"CONSTANT";      
        }else if(const Constant* C = dyn_cast<Constant>(valTo)){    
          name = "Const: " + C->getName().str();
        }else{
          //OS << "VALUE(" << *(j->v) << ")\n";
          name2 = "OTHER";
        }*/
        dot->insertEdge(name2, name); // OS << "\n\n====>>>" << *(j->v) << "<<======\n";
      }else{
        name2 = valTo->getName().str();
        dot->insertEdge(name,name2); //i.first->getName().str()
      }
    }
  }
  dot->toFile();
} 


/*
dot file class implementation

*/

// Instantiates the object and initializes the function name, 
// the dot file name and the first variable ID
dotFile::dotFile(std::string name){
  FunctionName = name;
  dotName = "cfg." + name + ".dot";
  dot << "digraph \"Transitive Closure\" {";
}

// Adds a std::string to the dot
void dotFile::insertLine(std::string str){
  dot << "\n\t\"" << str << "\" [shape=record, \n\t\tlabel=\"{" << str << ":\\l\\l\\l}\"]; ";
}

void dotFile::insertEdge(std::string str, std::string strX){
  dot << "\n\t\"" << str << "\" -> \"" << strX << "\";";
}

// Creates a dot file, writes the dot commands inside it and closes the file
void dotFile::toFile(){
  std::ofstream file;
  file.open(dotName.c_str());
  file << dot.str() + "\n}";
  file.close();
}

std::string dotFile::requireName(const Value *value){
 
  // Checks whether it is a constant value
  if ( isa<Constant> (value) ) {
  // Try to cast the value to an integer
    if ( const ConstantInt* number = dyn_cast<ConstantInt>(value))
      // Returns a string version of the integer value
      return (number->getValue().toString(10, true));

    if ( const ConstantFP* number = dyn_cast<ConstantFP>(value))
      // Returns a string version of a floating point value
      return number->getName().str();

    // Returns a string version of a global variable, expr, ConstantVector ...
    return (isa<GlobalValue>(value) ? "@" : "" ) + value->getName().str();
  } else {
  // Writes the value name if it is not a constant and already has a name
    std::string visibility = (! isa<GlobalValue>(value) ? "%" : "@" );
    if(value->hasName())
      return visibility + value->getName().str();

    // Adds a name (variable ID) to the value and write it
    //value->setName(Twine("ID")); ////getVarID()
    return visibility + value->getName().str();
  }
}

std::string dotFile::recreateName(const Instruction* i){
  
  unsigned nOp = i->getNumOperands();
  std::string name = std::string(i->getOpcodeName()) + " ";
  
  for(unsigned cont = 0; cont < nOp; cont++){ 
    if(cont>0)
      name += ", ";
    name += requireName(i->getOperand(cont));
  }
  return name;
}


void dotFile::addEdge(std::string from, std::string to){
  this->insertEdge(from,to);
}


