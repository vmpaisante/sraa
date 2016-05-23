#define DEBUG_TYPE "sraa"
#include "StrictRelationsAliasAnalysis.h"

#include <utility>

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
#include "../RangeAnalysis/RangeAnalysis.h"

using namespace llvm;

extern unsigned MAX_BIT_INT;
extern APInt Min;
extern APInt Max;
extern APInt Zero;

Primitives StrictRelations::P;


STATISTIC(NumVariables, "Number of variables");
STATISTIC(NumConstraints, "Number of constraints");
STATISTIC(NumResolve, "Number of resolve operations");
STATISTIC(NumQueries, "Number of alias queries received");
STATISTIC(NumNoAlias, "Number of NoAlias answers");

// Register this pass...
char StrictRelations::ID = 0;
static RegisterPass<StrictRelations> X("sraa",
                        "Strict relations alias analysis", false, false);
static RegisterAnalysisGroup<AliasAnalysis> E(X);

void StrictRelations::collectConstraintsFromModule(Module &M) {
  // Map that holds the comparisons anf sigmas
  // cmp -> leftside<truesigma, falsesigma> , rightside<truesigma, falsesigma>
  std::map<const CmpInst*, std::pair< std::pair<const Value*, const Value*>,
                              std::pair<const Value*, const Value*> > > sigmas;

  // Going through the module collecting constraints and sigmas
  for (Module::iterator m = M.begin(), me = M.end(); m != me; ++m) {
    for (Function::iterator b = m->begin(), be = m->end(); b != be; ++b) {
      for (BasicBlock::iterator I = b->begin(), ie = b->end(); I != ie; ++I) {
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
            variables[I]->constraints.insert(c);
            variables[op2]->constraints.insert(c);
            wle->add(c);
          }
          else if (r1.getLower().sgt(Zero)) {
            // Case x > 0 then y < a
            if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
            Constraint* c = new LT(wle, variables[op2], variables[I]);
            variables[I]->constraints.insert(c);
            variables[op2]->constraints.insert(c);
            wle->add(c);
          }
          else if (r1.getLower().sge(Zero)) {
            // Case x >= 0 then y <= a
            if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
            Constraint* c = new LE(wle, variables[op2], variables[I]);
            variables[I]->constraints.insert(c);
            variables[op2]->constraints.insert(c);
            wle->add(c);
          }
          else if (r1.getUpper().slt(Zero)) {
            // Case x < 0 then a < y
            if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
            Constraint* c = new LT(wle, variables[I], variables[op2]);
            variables[I]->constraints.insert(c);
            variables[op2]->constraints.insert(c);
            wle->add(c);
          }
          else if (r1.getUpper().sle(Zero)) {
            // Case x <= 0 then a <= y
            if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
            Constraint* c = new LE(wle, variables[I], variables[op2]);
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
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getLower().sgt(Zero)) {
            // Case y > 0 then x < a
            if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LT(wle, variables[op1], variables[I]);
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getLower().sge(Zero)) {
            // Case y >= 0 then x <= a
            if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LE(wle, variables[op1], variables[I]);
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getUpper().slt(Zero)) {
            // Case y < 0 then a < x
            if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LT(wle, variables[I], variables[op1]);
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getUpper().sle(Zero)) {
            // Case y <= 0 then a <= x
            if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LE(wle, variables[I], variables[op1]);
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
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sgt(Zero)) {
              // Case y > 0 then a < y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[I], variables[op2]);
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sge(Zero)) {
              // Case y >= 0 then a <= y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LE(wle, variables[I], variables[op2]);
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getUpper().slt(Zero)) {
              // Case y < 0 then y < a
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[op2], variables[I]);
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getUpper().sle(Zero)) {
              // Case y <= 0 then y <= a
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LE(wle, variables[op2], variables[I]);
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
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getUpper().sle(Zero)) {
              // Case y <= 0, a = (>0) - (<=0) then y < a 
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[op2], variables[I]);
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
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getUpper().sle(Zero)) {
              // Case y <= 0, a = (>=0) - (<=0) then y <= a 
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LE(wle, variables[op2], variables[I]);
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
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sgt(Zero)) {
              // Case y > 0, a = (<0) - (>0) then  a < y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[I], variables[op2]);
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sge(Zero)) {
              // Case y >= 0, a = (<0) - (>=0)  then a < y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[I], variables[op2]);
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
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sgt(Zero)) {
              // Case y > 0, a = (<=0) - (>0) then  a < y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LT(wle, variables[I], variables[op2]);
              variables[I]->constraints.insert(c);
              variables[op2]->constraints.insert(c);
              wle->add(c);
            }
            else if (r2.getLower().sge(Zero)) {
              // Case y >= 0, a = (<=0) - (>=0)  then a <= y
              if(!variables.count(op2)) variables[op2] =
                                          new StrictRelations::Variable(op2);
              Constraint* c = new LE(wle, variables[I], variables[op2]);
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
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getLower().sgt(Zero)) {
            // Case y > 0 then a < x
              if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LT(wle, variables[I], variables[op1]);
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getLower().sge(Zero)) {
            // Case y >= 0 then a <= x
              if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LE(wle, variables[I], variables[op1]);
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getUpper().slt(Zero)) {
            // Case y < 0 then x < a
              if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LT(wle, variables[op1], variables[I]);
            variables[I]->constraints.insert(c);
            variables[op1]->constraints.insert(c);
            wle->add(c);
          }
          else if (r2.getUpper().sle(Zero)) {
            // Case y <= 0 then x <= a
              if(!variables.count(op1)) variables[op1] =
                                          new StrictRelations::Variable(op1);
            Constraint* c = new LE(wle, variables[op1], variables[I]);
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
            variables[I]->constraints.insert(c);
            variables[base]->constraints.insert(c);
            wle->add(c);
          }
          else if (r.getLower().sgt(Zero)) {
            // Case p = b + (>0) then b < p
            if(!variables.count(base)) variables[base] =
                                        new StrictRelations::Variable(base);
            Constraint* c = new LT(wle, variables[base], variables[I]);
            variables[I]->constraints.insert(c);
            variables[base]->constraints.insert(c);
            wle->add(c);
          }
          else if (r.getLower().sge(Zero)) {
            // Case p = b + (>=0) then b <= p
            if(!variables.count(base)) variables[base] =
                                        new StrictRelations::Variable(base);
            Constraint* c = new LE(wle, variables[base], variables[I]);
            variables[I]->constraints.insert(c);
            variables[base]->constraints.insert(c);
            wle->add(c);
          }
          else if (r.getUpper().slt(Zero)) {
            // Case p = b + (<0) then p < b
            if(!variables.count(base)) variables[base] =
                                        new StrictRelations::Variable(base);
            Constraint* c = new LT(wle, variables[I], variables[base]);
            variables[I]->constraints.insert(c);
            variables[base]->constraints.insert(c);
            wle->add(c);
          }
          else if (r.getUpper().sle(Zero)) {
            // Case p = b + (<=0) then p <= b
            if(!variables.count(base)) variables[base] =
                                        new StrictRelations::Variable(base);
            Constraint* c = new LE(wle, variables[I], variables[base]);
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

          variables[I]->constraints.insert(c);
          variables[op]->constraints.insert(c);
          wle->add(c);
        }
        // Phi function
        else if(const PHINode* p = dyn_cast<PHINode>(I)) {
          std::set<StrictRelations::Variable*> vset;
          for(int i = 0, e = p->getNumIncomingValues(); i < e; i++) {
            const Value* op = p->getIncomingValue(i);
            if(!variables.count(op)) variables[op] =
                                          new StrictRelations::Variable(op);
            vset.insert(variables.at(op));
          }
          Constraint* c = new PHI(wle, variables[I], vset);

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

        variables[i.second.second.first]->constraints.insert(c);
        variables[i.second.first.first]->constraints.insert(c);
        wle->add(c);
      }
      if(variables.count(i.second.first.second) and
         variables.count(i.second.second.second)) {
        c = new LE(wle, variables[i.second.first.second],
                        variables[i.second.second.second]);

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

        variables[i.second.second.first]->constraints.insert(c);
        variables[i.second.first.first]->constraints.insert(c);
        wle->add(c);
      }
      if(variables.count(i.second.first.second) and
         variables.count(i.second.second.second)) {
        c = new LT(wle, variables[i.second.first.second],
                        variables[i.second.second.second]);

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
      
        variables[i.second.first.first]->constraints.insert(c);
        variables[i.second.second.first]->constraints.insert(c);
        wle->add(c);
      }
      if(variables.count(i.second.second.second) and
         variables.count(i.second.first.second)) {
        c = new LE(wle, variables[i.second.second.second],
                        variables[i.second.first.second]);

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

        variables[i.second.first.first]->constraints.insert(c);
        variables[i.second.second.first]->constraints.insert(c);
        wle->add(c);
      }
      if(variables.count(i.second.second.second) and
         variables.count(i.second.first.second)) {
        c = new LT(wle, variables[i.second.second.second],
                        variables[i.second.first.second]);

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

        variables[i.second.first.second]->constraints.insert(c);
        variables[i.second.second.second]->constraints.insert(c);
        wle->add(c);
      }
    }
  }
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
// Builds the program's dependence graph
// Currently works only for GEPs
// TODO: Make it work for the whole program
void StrictRelations::buildDepGraph(Module &M) {
  dg = new DepGraph();
  // Going through the module building the dependence graph
  for (Module::iterator m = M.begin(), me = M.end(); m != me; ++m) {
    for (Function::iterator b = m->begin(), be = m->end(); b != be; ++b) {
      for (BasicBlock::iterator I = b->begin(), ie = b->end(); I != ie; ++I) {
        // GEP Instruction
        if (const GetElementPtrInst* p = dyn_cast<GetElementPtrInst>(I)) {
          // Getting base pointer
          const Value* base = p->getPointerOperand();
          // Geting bit range of offset
          Range r = processGEP (base, p->idx_begin(), p->idx_end());
          
          if(!variables.count(p)) variables[p] =
                                        new StrictRelations::Variable(p);
          if(!variables.count(base)) variables[base] =
                                        new StrictRelations::Variable(base);

          dg->addVariable(variables[p]);
          dg->addVariable(variables[base]);
          dg->addEdge(variables[base], variables[p], r, p);
        } else if(isa<BitCastInst>(&(*I))
                  or isa<SExtInst>(&(*I))
                  or isa<ZExtInst>(&(*I))){
          // Coalesce variables
          const Value* op = I->getOperand(0);
          if(!variables.count(op)) variables[op] =
                                          new StrictRelations::Variable(op);
          if(!variables.count(I)) variables[I] =
                                          new StrictRelations::Variable(I);
          dg->coalesce(variables[I], variables[op]);
        } else if (isa<PHINode>(&(*I)) && (I->getNumOperands() == 1) ) {
          const PHINode* p = dyn_cast<PHINode>(I);
          // Coalesce variables
          const Value* op = p->getIncomingValue(0);
          if(!variables.count(op)) variables[op] =
                                          new StrictRelations::Variable(op);
          if(!variables.count(I)) variables[I] =
                                          new StrictRelations::Variable(I);
          dg->coalesce(variables[I], variables[op]);
        }
      }
    }
  }
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
StrictRelations::CompareResult StrictRelations::compareGEPs(
                                  const GetElementPtrInst* G1,
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
  return r;
}

// Collects constraints from the dependence graph
// Currently works only for GEPs
// TODO: Make it work for the whole program
void StrictRelations::collectConstraintsFromDepGraph() {
  std::set<DepGraph::DepNode*> nodes;
  for(auto i : *dg) nodes.insert(i.second);
  for(auto i : nodes) {
    for(auto ji = i->edges.begin(), je = i->edges.end(); ji != je; ji++) {
      DepGraph::DepEdge* j = *ji;
      auto ki = ji;
      ki++;
      for(auto ke = i->edges.end(); ki != ke; ki++) {
        DepGraph::DepEdge* k = *ki;
        // Edges j and k. Base pointer i.
        if(j->range.getUpper().slt(k->range.getLower())) {
          Variable* jv = *(j->target->variables.begin());
          Variable* kv = *(k->target->variables.begin());
          Constraint* c = new LT(wle, jv, kv);
          jv->constraints.insert(c);
          kv->constraints.insert(c);
          wle->add(c);
        } else if (compareGEPs(j->gep, k->gep) == L) {
          Variable* jv = *(j->target->variables.begin());
          Variable* kv = *(k->target->variables.begin());
          Constraint* c = new LT(wle, jv, kv);
          jv->constraints.insert(c);
          kv->constraints.insert(c);
          wle->add(c);
        } else if (j->range.getLower().sgt(k->range.getUpper())) {
          Variable* jv = *(j->target->variables.begin());
          Variable* kv = *(k->target->variables.begin());
          Constraint* c = new LT(wle, kv, jv);
          jv->constraints.insert(c);
          kv->constraints.insert(c);
          wle->add(c);
        } else if (compareGEPs(j->gep, k->gep) == G) {
          Variable* jv = *(j->target->variables.begin());
          Variable* kv = *(k->target->variables.begin());
          Constraint* c = new LT(wle, kv, jv);
          jv->constraints.insert(c);
          kv->constraints.insert(c);
          wle->add(c);
        }
      }
    }
  }
}

bool StrictRelations::runOnModule(Module &M) {
  InitializeAliasAnalysis(this, &M.getDataLayout());
  RA = &getAnalysis<InterProceduralRACousot>();
  wle = new WorkListEngine();
  // Phase 1
  DEBUG(errs() << "Collecting constraints.\n");
  collectConstraintsFromModule(M);
  DEBUG(wle->printConstraints(errs()));
  // Phase 2
  DEBUG(errs() << "Running WorkList engine.\n");
  wle->solve();
  // Phase 3
  DEBUG(errs() << "Collecting the dependence graph.\n");
  buildDepGraph(M);
  collectConstraintsFromDepGraph();
  // Phase 4
  DEBUG(errs() << "Running WorkList engine again.\n");
  wle->solve();

  DEBUG(printAllStrictRelations(errs()));

  NumVariables = variables.size();
  NumConstraints = wle->getNumConstraints();
  return false;
}

void StrictRelations::printAllStrictRelations(raw_ostream &OS){
  OS << "Strict Relations:\n";
  OS << "-------------------------------------------------\n";
  for(auto i : variables) {
    OS << "Variable: " ;
    if(i.first->getValueName() == NULL) OS << *(i.first);
    else OS << i.first->getName();
    OS << "\nLT: {";
    if(i.second->LT.empty()) OS << "E";
    for(auto j : i.second->LT) {
      if(j->v->getValueName() == NULL) OS << *(j->v);
      else OS << j->v->getName();
      OS << "; ";
    }
    OS << "}\nGT: {";
    if(i.second->GT.empty()) OS << "E";
    for(auto j : i.second->GT) {
      if(j->v->getValueName() == NULL) OS << *(j->v);
      else OS << j->v->getName();
      OS << "; ";
    }
    OS << "}\n";
  }
  OS << "-------------------------------------------------\n";
}

void StrictRelations::Variable::printStrictRelations(raw_ostream &OS){
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

void StrictRelations::getAnalysisUsage(AnalysisUsage &AU) const {
  AliasAnalysis::getAnalysisUsage(AU);
  AU.addRequired<InterProceduralRA<Cousot> >();
  AU.setPreservesAll();
}

AliasResult 
StrictRelations::alias(const MemoryLocation &LocA, const MemoryLocation &LocB){
  NumQueries++;
  const Value *p1, *p2;
  p1 = LocA.Ptr;
  p2 = LocB.Ptr;
  if(!variables.count(p1)) variables[p1] = new StrictRelations::Variable(p1);
  if(!variables.count(p2)) variables[p2] = new StrictRelations::Variable(p2);
  Variable* v1 = variables[p1];
  Variable* v2 = variables[p2];
  if(v1->LT.count(v2) or v1->GT.count(v2)) {
    NumNoAlias++;
    return NoAlias;
  }
  return AliasAnalysis::alias(LocA, LocB); 
}

// Constraints definitions

// LT(x) U= {y}
void insertLT(StrictRelations::Variable* x,
                               StrictRelations::Variable* y,
                            std::set<StrictRelations::Variable*> &changed) {
  if(!x->LT.count(y) and x != y) {
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
                            std::set<StrictRelations::Variable*> &changed) {
  if(!x->GT.count(y) and x != y) {
    x->GT.insert(y);
    changed.insert(x);
    if(!y->LT.count(x)) {
      y->LT.insert(x);
      changed.insert(y);
    }
  }
}

void LT::resolve() const {
  // x < y
  //DEBUG(errs() << "Resolving: ");
  //DEBUG(print(errs()));
  //DEBUG(errs() << "Before: \n");
  //DEBUG(left->printStrictRelations(errs()));
  //DEBUG(right->printStrictRelations(errs()));
  std::set<StrictRelations::Variable*> changed;
  
  // LT(y) U= LT(x) U {x}
  insertLT(right, left, changed);

  for(auto i : left->LT) {
    insertLT(right, i, changed);
  }
  // GT(x) U= GT(y) U {y}
  insertGT(left, right, changed);
  for(auto i : right->GT) {
    insertGT(left, i, changed);
  }
  // Adding back constraints from changed abstract values
  for(auto c : changed)
    for(auto i : c->constraints)
      if(i != this) engine->add(i, false);

  //DEBUG(errs() << "After: \n");
  //DEBUG(left->printStrictRelations(errs()));
  //DEBUG(right->printStrictRelations(errs()));
}  
void LE::resolve() const { 
  // x <= y
  //DEBUG(errs() << "Resolving: ");
  //DEBUG(print(errs()));
  //DEBUG(errs() << "Before: \n");
  //DEBUG(left->printStrictRelations(errs()));
  //DEBUG(right->printStrictRelations(errs()));
  
  std::set<StrictRelations::Variable*> changed;
  
  // LT(y) U= LT(x)
  for(auto i : left->LT) {
    insertLT(right, i, changed);
  }
  // GT(x) U= GT(y)
  for(auto i : right->GT) {
    insertGT(left, i, changed);
  }
  // Adding back constraints from changed abstract values
  for(auto c : changed)
    for(auto i : c->constraints)
      if(i != this) engine->add(i, false);

  //DEBUG(errs() << "After: \n");
  //DEBUG(left->printStrictRelations(errs()));
  //DEBUG(right->printStrictRelations(errs()));
}
void REQ::resolve() const { 
  // x = y
  //DEBUG(errs() << "Resolving: ");
  //DEBUG(print(errs()));
  //DEBUG(errs() << "Before: \n");
  //DEBUG(left->printStrictRelations(errs()));
  //DEBUG(right->printStrictRelations(errs()));

  std::set<StrictRelations::Variable*> changed;
  // LT(x) U= LT(y)
  for(auto i : right->LT) {
    insertLT(left, i, changed);
  }
  // LT(y) U= LT(x)
  for(auto i : left->LT) {
    insertLT(right, i, changed);
  }
  // GT(x) U= GT(y)
  for(auto i : right->GT) {
    insertGT(left, i, changed);
  }
  // GT(y) U= GT(x)
  for(auto i : left->GT) {
    insertGT(right, i, changed);
  }
  // Adding back constraints from changed abstract values
  for(auto c : changed)
    for(auto i : c->constraints)
      if(i != this) engine->add(i, false);
  
  //DEBUG(errs() << "After: \n");
  //DEBUG(left->printStrictRelations(errs()));
  //DEBUG(right->printStrictRelations(errs()));
}

void EQ::resolve() const { 
  // x = y
  //DEBUG(errs() << "Resolving: ");
  //DEBUG(print(errs()));
  //DEBUG(errs() << "Before: \n");
  //DEBUG(left->printStrictRelations(errs()));
  //DEBUG(right->printStrictRelations(errs()));
  std::set<StrictRelations::Variable*> changed;
  // LT(x) U= LT(y)
  for(auto i : right->LT) {
    insertLT(left, i, changed);
  }
  // GT(x) U= GT(y)
  for(auto i : right->GT) {
    insertGT(left, i, changed);
  }
  // Adding back constraints from changed abstract values
  for(auto c : changed)
    for(auto i : c->constraints)
      if(i != this) engine->add(i, false);
  
  //DEBUG(errs() << "After: \n");
  //DEBUG(left->printStrictRelations(errs()));
  //DEBUG(right->printStrictRelations(errs()));
}

std::set<StrictRelations::Variable*> intersect
                          (std::set<StrictRelations::Variable*> &s1,
                           std::set<StrictRelations::Variable*> &s2) {
  std::set<StrictRelations::Variable*> r;
  for(auto i : s1) if(s2.count(i)) r.insert(i);
  return r;
}

std::set<StrictRelations::Variable*> unionize
                          (std::set<StrictRelations::Variable*> &s1,
                           std::set<StrictRelations::Variable*> &s2) {
  std::set<StrictRelations::Variable*> r;
  for(auto i : s1) r.insert(i);
  for(auto i : s2) r.insert(i);
  return r;
}

void PHI::resolve() const { 
  // x = I( xi )
  //DEBUG(errs() << "Resolving: ");
  //DEBUG(print(errs()));
  //DEBUG(errs() << "Before: \n");
  //DEBUG(left->printStrictRelations(errs()));
  //for(auto i : operands) DEBUG(i->printStrictRelations(errs()));
  std::set<StrictRelations::Variable*> changed;
  // Growth checks
  bool gu = false, gd = false;
  for (auto i : operands) if (i->LT.count(left)) { gu = true; break; }
  for (auto i : operands) if (i->GT.count(left)) { gd = true; break; }
  std::set<StrictRelations::Variable*> ULT, UGT;
  // If it can only grow up
  if(gu and !gd) {
    // LT(x) U= I( LT(xj) ) U U( LT(xk) ), where x !E LT(xj) and x E LT(xk)
    // Intersection part
    auto i = operands.begin();
    do {
      ULT = (*i)->LT;
      i++;
    } while (!ULT.count(left) and i != operands.end());
    for (auto e = operands.end(); i != e; i++)
      if(!(*i)->LT.count(left)) ULT = intersect(ULT, (*i)->LT);
    // Union part
    for(auto i : operands) if(i->LT.count(left)) ULT = unionize(ULT, i->LT);
    
  } else {
    // LT(x) U= I( LT(xi) )
    auto i = operands.begin();
    ULT = (*i)->LT;
    i++;
    for (auto e = operands.end(); i != e; i++) ULT = intersect(ULT, (*i)->LT);
  }
  // If it can only grow down
  if(!gu and gd) {
    // GT(x) U= I( GT(xj) ) U U( GT(xk) ), where x !E GT(xj) and x E GT(xk)
    // Intersection part
    auto i = operands.begin();
    do {
    UGT = (*i)->GT;
    i++;
    } while (!UGT.count(left) and i != operands.end());
    for (auto e = operands.end(); i != e; i++)
      if(!(*i)->GT.count(left)) UGT = intersect(UGT, (*i)->GT);
    // Union part
    for(auto i : operands) if(i->GT.count(left)) UGT = unionize(UGT, i->GT);
    
  } else {
    // GT(x) U= I( GT(xi) )
    auto i = operands.begin();
    UGT = (*i)->GT;
    i++;
    for (auto e = operands.end(); i != e; i++) UGT = intersect(UGT, (*i)->GT);
  }
  // Remove left from ULT and UGT
  ULT.erase(left);
  UGT.erase(left);
  // U= part
  for(auto i : ULT) {
    insertLT(left, i, changed);
  }
  for(auto i : UGT) {
    insertGT(left, i, changed);
  }

  // Adding back constraints from changed abstract values
  for(auto c : changed)
    for(auto i : c->constraints)
      if(i != this) engine->add(i, false);

  //DEBUG(errs() << "After: \n");
  //DEBUG(left->printStrictRelations(errs()));
  //for(auto i : operands) DEBUG(i->printStrictRelations(errs()));
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

// WorkListEngine definitions

void WorkListEngine::solve() {
  while(!worklist.empty()) {
    const Constraint* c = worklist.front();
    worklist.pop();
    constraints[c] = false;
    c->resolve();
    NumResolve++;
  }
}

void WorkListEngine::add(Constraint* C, bool isnew) {
  if(isnew) constraints[C] = false;
  if(!constraints.at(C)) {
    worklist.push(C);
    constraints[C] = true;
  }
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
// DepGraph definitions
// Adds a variable to the dependence graph
void DepGraph::addVariable(StrictRelations::Variable* V) {
  if(!nodes.count(V)) {
    nodes[V] = new DepNode();
    nodes[V]->variables.insert(V);
  }
}
// In constraints x = y is necessary to coalesce the nodes
void DepGraph::coalesce (StrictRelations::Variable* V1,
StrictRelations::Variable* V2) {
  if(!nodes.count(V1)) {
    nodes[V1] = new DepNode();
    nodes[V1]->variables.insert(V1);
  }
  if(!nodes.count(V2)) {
    nodes[V2] = new DepNode();
    nodes[V2]->variables.insert(V2);
  }

  for(auto i : nodes[V1]->variables) nodes[V2]->variables.insert(i);
  for(auto i : nodes[V1]->edges) nodes[V2]->edges.insert(i);
  DepNode* aux = nodes[V1];
  DepNode* aux2 = nodes[V2];
  for(auto i : aux->inedges)
    i->target = aux2;
  nodes[V1] = aux2;
  delete aux;
}
//In the case of a GEP A = B + R
void DepGraph::addEdge(StrictRelations::Variable* B,
StrictRelations::Variable* A, Range R, const GetElementPtrInst* G) {
  // Check if they are in different node
  if (nodes[A] == nodes[B]) return;
  // if range is [0,0] we must coalesce
  if (R.getLower().eq(Zero) and R.getUpper().eq(Zero)) {
    coalesce(A, B);
    return;
  }
  DepEdge* edge = new DepEdge();
  edge->target = nodes[A];
  edge->sign = Addition;
  edge->operation = Addition;
  edge->operand = NULL;
  edge->range = R;
  edge->gep = G;
  nodes[B]->edges.insert(edge);
  nodes[A]->inedges.insert(edge);
}
