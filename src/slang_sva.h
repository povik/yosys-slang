#pragma once
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include <iostream>


namespace ast = slang::ast;


void handle_sva(const ast::PropertySymbol &sym);

class SVAVisitor : public ast::ASTVisitor<SVAVisitor, false, false>{
public:
      // Use AssertionExpr::visit() to dispatch
      void handle(const ast::AssertionExpr& expr) {
          expr.visit(*this);
      }

      // Handler for each type
      void handle(const ast::SimpleAssertionExpr& e) {
          std::cout << "Simple expr\n";
          // e.expr is the boolean signal
      }

      void handle(const ast::SequenceConcatExpr& e) {
          std::cout << "Concat with " << e.elements.size() << " elements\n";
          for (auto& elem : e.elements) {
              std::cout << "  delay: " << elem.delay.min;
              if (elem.delay.max) std::cout << ":" << *elem.delay.max;
              std::cout << "\n";
              elem.sequence->visit(*this);  // recurse
          }
      }

      void handle(const ast::BinaryAssertionExpr& e) {
          std::cout << "Binary op: " << toString(e.op) << "\n";
          e.left.visit(*this);
          e.right.visit(*this);
      }

      void handle(const ast::UnaryAssertionExpr& e) {
          std::cout << "Unary op: " << toString(e.op) << "\n";
          e.expr.visit(*this);
      }

      void handle(const ast::ClockingAssertionExpr& e) {
          std::cout << "Clocked assertion\n";
          // Extract clock from e.clocking
          if (auto* sig = e.clocking.as_if<ast::SignalEventControl>()) {
              std::cout << "  clock edge: " << toString(sig->edge) << "\n";
          }
          e.expr.visit(*this);
      }

      void handle(const ast::DisableIffAssertionExpr& e) {
          std::cout << "Disable iff\n";
          e.expr.visit(*this);
      }

      void handle(const ast::AbortAssertionExpr& e) {
          std::cout << (e.action == ast::AbortAssertionExpr::Accept ? "accept_on" : "reject_on") << "\n";
          e.expr.visit(*this);
      }

      void handle(const ast::ConditionalAssertionExpr& e) {
          std::cout << "if-else property\n";
          e.ifExpr.visit(*this);
          if (e.elseExpr) e.elseExpr->visit(*this);
      }

      void handle(const ast::FirstMatchAssertionExpr& e) {
          std::cout << "first_match\n";
          e.seq.visit(*this);
      }

      void handle(const ast::StrongWeakAssertionExpr& e) {
          std::cout << (e.strength == ast::StrongWeakAssertionExpr::Strong ? "strong" : "weak") << "\n";
          e.expr.visit(*this);
      }

      void handle(const ast::SequenceWithMatchExpr& e) {
          std::cout << "Sequence with match\n";
          e.expr.visit(*this);
      }

      void handle(const ast::CaseAssertionExpr& e) {
          std::cout << "case property\n";
          for (auto& item : e.items) {
              item.body->visit(*this);
          }
          if (e.defaultCase) e.defaultCase->visit(*this);
      }

      void handle(const ast::InvalidAssertionExpr&) {
          std::cout << "Invalid\n";
      }
  };

