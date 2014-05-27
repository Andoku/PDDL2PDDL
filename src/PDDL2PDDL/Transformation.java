package PDDL2PDDL;

import java.util.*;

import pddl4j.PDDLObject;
import pddl4j.RequireKey;
import pddl4j.Source;
import pddl4j.InvalidExpException;
import pddl4j.exp.*;
import pddl4j.exp.term.*;
import pddl4j.exp.action.*;
import pddl4j.exp.fcomp.*;
import pddl4j.exp.time.TimedExp;

class Transformation {
	
	static Exp replaceForall(Exp e, PDDLObject problem) {
		switch (e.getExpID()) {
	    case AND: case OR:
	        ListExp listExp = (ListExp) e;
			for (int i = 0; i < listExp.size(); i++) {
				listExp.set(i, replaceForall(listExp.get(i), problem));
			}
			return listExp;
		case FORALL:
			QuantifiedExp quantr = (QuantifiedExp) e;
			quantr.setExp(replaceForall(quantr.getExp(), problem));
			AndExp andExp = new AndExp();
			Iterator<Variable> vari = quantr.iterator();
			Variable var = vari.next();
			System.out.println(var);
			System.out.println(quantr.getExp());
			if (quantr.getExp().occurs(var)) {
				for (Iterator<Constant> obj = problem.constantsIterator(); obj.hasNext(); ) {
					Substitution sigma = new Substitution();
					sigma.bind(var, obj.next());
					andExp.add(quantr.getExp().apply(sigma));
				}
			} else {
				andExp.add(quantr.getExp());
			}
			if (vari.hasNext()) {
				vari.remove();
				quantr.setExp(andExp);
				return replaceForall(quantr, problem);
			} else {
				return andExp;
			}
		case EXIST:
			QuantifiedExp q = (QuantifiedExp) e;
			q.setExp(replaceForall(q.getExp(), problem));
			return q;
		case WHEN:
			WhenExp whenExp = (WhenExp) e;
			whenExp.setCondition(replaceForall(whenExp.getCondition(), problem));
			whenExp.setEffect(replaceForall(whenExp.getEffect(), problem));
			return whenExp;
	    case NOT:
	        NotExp notExp = (NotExp) e;
			notExp.setExp(replaceForall(notExp.getExp(), problem));
			return notExp;
		case TIMED_EXP:
			TimedExp timedExp = (TimedExp) e;
			timedExp.setExp(replaceForall(timedExp.getExp(), problem));
			return timedExp;
		case IMPLY:
			ImplyExp implyExp = (ImplyExp) e;
			implyExp.setHead(replaceForall(implyExp.getHead(), problem));
			implyExp.setBody(replaceForall(implyExp.getBody(), problem));
			return implyExp;
		case DERIVED_PREDICATE:
			DerivedPredicate derivedPredicate = (DerivedPredicate) e;
			derivedPredicate.setBody(replaceForall(derivedPredicate.getBody(), problem));
			return derivedPredicate;
		case ASSIGN_OP: case COND_EXP: case F_COMP:
		case ATOMIC_FORMULA: case METRIC_EXP: case TERM:
			return e;
		}
		return e;
	}

	static Exp moveQuantifierForward(Exp e) {
		switch (e.getExpID()) {
	    case AND: case OR:
	        ListExp listExp = (ListExp) e;
			for (int i = 0; i < listExp.size(); i++) {
				listExp.set(i, moveQuantifierForward(listExp.get(i)));
			}
			return listExp;
		case FORALL: case EXIST:
			QuantifiedExp quantr = (QuantifiedExp) e;
			quantr.setExp(moveQuantifierForward(quantr.getExp()));
			return quantr;
		case WHEN:
			WhenExp whenExp = (WhenExp) e;
			whenExp.setCondition(moveQuantifierForward(whenExp.getCondition()));
			whenExp.setEffect(moveQuantifierForward(whenExp.getEffect()));
			return whenExp;
	    case NOT:
	        NotExp notExp = (NotExp) e;
			notExp.setExp(moveQuantifierForward(notExp.getExp()));
			return notExp;
		case TIMED_EXP:
			TimedExp timedExp = (TimedExp) e;
			timedExp.setExp(moveQuantifierForward(timedExp.getExp()));
			return timedExp;
		case IMPLY:
			ImplyExp implyExp = (ImplyExp) e;
			implyExp.setHead(moveQuantifierForward(implyExp.getHead()));
			implyExp.setBody(moveQuantifierForward(implyExp.getBody()));
			return implyExp;
		case DERIVED_PREDICATE:
			DerivedPredicate derivedPredicate = (DerivedPredicate) e;
			derivedPredicate.setBody(moveQuantifierForward(derivedPredicate.getBody()));
			return derivedPredicate;
		case F_COMP: case ASSIGN_OP: case COND_EXP: 
		case ATOMIC_FORMULA: case METRIC_EXP: case TERM:
			return e;
		}
		return e;
		//return e.toDisjunctiveNormalForm();
	}

	static boolean hasExp(Exp e, ExpID id) {
		if (e.getExpID().equals(id))
			return true;
	
		switch (e.getExpID()) {
	    case AND: case OR:
	        ListExp listExp = (ListExp) e;
			for (int i = 0; i < listExp.size(); i++) {
				if (hasExp(listExp.get(i), id))
					return true;
			}
	        break;
		case FORALL: case EXIST:
			QuantifiedExp quantr = (QuantifiedExp) e;
			if (hasExp(quantr.getExp(), id))
				return true;
			break;
		case WHEN:
			WhenExp whenExp = (WhenExp) e;
			if(hasExp(whenExp.getCondition(), id))
				return true;
			if(hasExp(whenExp.getEffect(), id))
				return true;
			break;
	    case NOT:
	        NotExp notExp = (NotExp) e;
			if(hasExp(notExp.getExp(), id))
				return true;
	        break;
		case TIMED_EXP:
			TimedExp timedExp = (TimedExp) e;
			if(hasExp(timedExp.getExp(), id))
				return true;
			break;
		case IMPLY:
			ImplyExp implyExp = (ImplyExp) e;
			if(hasExp(implyExp.getHead(), id))
				return true;
			if(hasExp(implyExp.getBody(), id))
				return true;
			break;
		case DERIVED_PREDICATE:
			DerivedPredicate derivedPredicate = (DerivedPredicate) e;
			if(hasExp(derivedPredicate.getHead(), id))
				return true;
			if(hasExp(derivedPredicate.getBody(), id))
				return true;
			break;
		case F_COMP: case ASSIGN_OP: case COND_EXP: 
		case ATOMIC_FORMULA: case METRIC_EXP: case TERM:
			break;
		}
		return false;
	}



	static Exp replaceEqualityOperator(Exp e, String eq_predicate) {
		switch (e.getExpID()) {
	    case AND: case OR:
	        ListExp listExp = (ListExp) e;
			for (int i = 0; i < listExp.size(); i++) {
				listExp.set(i, replaceEqualityOperator(listExp.get(i), eq_predicate));
			}
			return listExp;
		case FORALL: case EXIST:
			QuantifiedExp quantr = (QuantifiedExp) e;
			quantr.setExp(replaceEqualityOperator(quantr.getExp(), eq_predicate));
			return quantr;
		case WHEN:
			WhenExp whenExp = (WhenExp) e;
			whenExp.setCondition(replaceEqualityOperator(whenExp.getCondition(), eq_predicate));
			whenExp.setEffect(replaceEqualityOperator(whenExp.getEffect(), eq_predicate));
			return whenExp;
	    case NOT:
	        NotExp notExp = (NotExp) e;
			notExp.setExp(replaceEqualityOperator(notExp.getExp(), eq_predicate));
			return notExp;
		case TIMED_EXP:
			TimedExp timedExp = (TimedExp) e;
			timedExp.setExp(replaceEqualityOperator(timedExp.getExp(), eq_predicate));
			return timedExp;
		case IMPLY:
			ImplyExp implyExp = (ImplyExp) e;
			implyExp.setHead(replaceEqualityOperator(implyExp.getHead(), eq_predicate));
			implyExp.setBody(replaceEqualityOperator(implyExp.getBody(), eq_predicate));
			return implyExp;
		case DERIVED_PREDICATE:
			DerivedPredicate derivedPredicate = (DerivedPredicate) e;
			derivedPredicate.setBody(replaceEqualityOperator(derivedPredicate.getBody(), eq_predicate));
			return derivedPredicate;
		case F_COMP:
			FCompExp fcomp = (FCompExp) e;
			if (fcomp.getOp().equals(Comp.EQUAL) && fcomp.getArg1().getTermID().equals(TermID.VARIABLE) 
	                                             && fcomp.getArg2().getTermID().equals(TermID.VARIABLE)) {											
				AtomicFormula predicate = new AtomicFormula(eq_predicate);
				predicate.add(fcomp.getArg1());
				predicate.add(fcomp.getArg2());
				return predicate;
			} else {
				return e;
			}
		case ASSIGN_OP: case COND_EXP: 
		case ATOMIC_FORMULA: case METRIC_EXP: case TERM:
			return e;
		}
		return e;
	}

}