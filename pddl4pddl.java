import java.io.File;
import java.io.FileNotFoundException;
import java.util.*;

import pddl4j.ErrorManager;
import pddl4j.PDDLObject;
import pddl4j.Parser;
import pddl4j.RequireKey;
import pddl4j.Source;
import pddl4j.ErrorManager.Message;
import pddl4j.InvalidExpException;
import pddl4j.exp.*;
import pddl4j.exp.term.*;
import pddl4j.exp.action.*;
import pddl4j.exp.fcomp.*;
import pddl4j.exp.time.TimedExp;



class Pddl4pddl {
public static void main(String[] args) throws Exception {
	
    if (args.length != 3) {
        System.err.println("Invalid command line");
    } else {
        Parser parser = new Parser();
		
		PDDLObject domain = parser.parse(new File(args[1]));
		PDDLObject problem = parser.parse(new File(args[2]));
		PDDLObject obj = parser.link(domain, problem);
		
		ErrorManager mgr = parser.getErrorManager();
        if (mgr.contains(Message.ERROR)) {
            mgr.print(Message.ALL);
        } else {
            mgr.print(Message.WARNING);
            System.out.println("\nParsing domain done successfully ...");
            System.out.println("Parsing problem done successfully ...\n");
        }

		if (args[0].equals(":equality")) {
			transformEquality(domain, problem);
		} else if (args[0].equals(":disjunctive-preconditions")) {
			transformDisjunctivePreconditions(domain, problem);
		} else if (args[0].equals(":universal-preconditions")){
			transformUniversalPreconditions(domain, problem);
		} else {
			System.err.println("Invalid command line");
		}
		
		System.out.println(problem.toString());
		System.out.println();
		System.out.println(domain.toString());
		
    }
}

static void transformUniversalPreconditions(PDDLObject domain, PDDLObject problem) {
	for (Iterator<ActionDef> iter = domain.actionsIterator(); iter.hasNext(); ) {
		//todo: add durative actions support
		Action action = (Action) iter.next();
		Exp precondition = replaceForall(action.getPrecondition(), problem);
		action.setPrecondition(precondition);
		Exp effect = replaceForall(action.getEffect(), problem);
		action.setEffect(effect);
	}
	//todo: replace in goal
}

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

static void transformDisjunctivePreconditions(PDDLObject domain, PDDLObject problem) {
	// change requirments

	String goal_predicate_name = "goal_predicate"; // This shpuld be unique
	
	List<InitEl> init = problem.getInit();
	AtomicFormula goal_predicate = new AtomicFormula(goal_predicate_name);
	domain.addPredicate(goal_predicate);
	
	Exp goal_exp = problem.getGoal();
	goal_exp = goal_exp.toDisjunctiveNormalForm();
	
	if (hasExp(goal_exp, ExpID.OR)) {
		problem.setGoal(goal_predicate);
		ListExp listExp = (ListExp) goal_exp;
		for (int i = 0; i < listExp.size(); i++) {
			Exp precondition = listExp.get(i);
			String action_name = "action_name" + i; //should be unique
			Action action = new Action(action_name);
			action.setEffect(goal_predicate);
			action.setPrecondition(precondition);
			domain.addAction(action);
		}
	}
	 
	List<Action> newActions = new ArrayList<Action>();
	for (Iterator<ActionDef> iter = domain.actionsIterator(); iter.hasNext(); ) {
		ActionDef action = iter.next();
		Exp precondition = ((Action) action).getPrecondition();
		if (hasExp(precondition, ExpID.OR)) {
			precondition = precondition.toDisjunctiveNormalForm();
			//System.out.println(precondition.toString());
			//TODO: inside quantr, inside when, imply
			ListExp listExp = (ListExp) precondition;
			for (int i = 0; i < listExp.size(); i++) {
				Exp disjunct = listExp.get(i);
				String action_name = "action_name" + i + i; //should be unique
				Action new_action = new Action(action_name);
				new_action.setEffect(((Action) action).getEffect());
				new_action.setPrecondition(disjunct);
				new_action.setParameters(action.getParameters());
				newActions.add(new_action);
			}
			iter.remove();
		}
	}
	for (Action newAction : newActions)
		domain.addAction(newAction);
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


static void transformEquality(PDDLObject domain, PDDLObject problem) {
	
	// change requirments
	
	String eq_predicate = "eq"; // This shpuld be unique
	
	AtomicFormula eq_prdct = new AtomicFormula(eq_predicate);
	Constant o1 = new Constant("?o1");
	Constant o2 = new Constant("?o2");
	eq_prdct.add(o1);
	eq_prdct.add(o2);
	domain.addPredicate(eq_prdct);
	
	List<InitEl> init = problem.getInit();	
	for (Iterator<Constant> iter = problem.constantsIterator(); iter.hasNext(); ) {
		Constant object = iter.next();
		AtomicFormula predicate = new AtomicFormula(eq_predicate);
		predicate.add(object);
		predicate.add(object);
		init.add(predicate);
	}
	
	for (Iterator<ActionDef> iter = domain.actionsIterator(); iter.hasNext(); ) {
		//todo: add durative actions support
		Action action = (Action) iter.next();
		Exp precondition = replaceEqualityOperator(action.getPrecondition(), eq_predicate);
		action.setPrecondition(precondition);
		Exp effect = replaceEqualityOperator(action.getEffect(), eq_predicate);
		action.setEffect(effect);
	}
	//todo: replace in goal
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