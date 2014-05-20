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
import pddl4j.exp.AndExp;
import pddl4j.exp.OrExp;
import pddl4j.exp.AtomicFormula;
import pddl4j.exp.Exp;
import pddl4j.exp.ListExp;
import pddl4j.exp.ExpID;
import pddl4j.exp.term.TermID;
import pddl4j.exp.InitEl;
import pddl4j.exp.Literal;
import pddl4j.exp.NotAtomicFormula;
import pddl4j.exp.NotExp;
import pddl4j.exp.WhenExp;
import pddl4j.exp.time.TimedExp;
import pddl4j.exp.ImplyExp;
import pddl4j.exp.DerivedPredicate;
import pddl4j.exp.term.Substitution;
import pddl4j.exp.term.Variable;
import pddl4j.exp.term.Term;
import pddl4j.exp.action.Action;
import pddl4j.exp.action.ActionDef;
import pddl4j.exp.action.AbstractActionDef;
import pddl4j.exp.action.ActionID;
import pddl4j.exp.fcomp.FCompExp;
import pddl4j.exp.fcomp.Comp;
import pddl4j.exp.QuantifiedExp;
import pddl4j.exp.ForallExp;
import pddl4j.exp.AbstractExp;
import pddl4j.exp.term.Constant;


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
		} else {
			System.err.println("Invalid command line");
		}
		
		System.out.println(problem.toString());
		System.out.println();
		System.out.println(domain.toString());
		
    }
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

static boolean hasExp(Exp e, ExpID id) {
	if (e.getExpID().equals(id))
		return true;
	
	switch (e.getExpID()) {
    case AND: case OR:
        ListExp listExp = (ListExp) e;
		for (int i = 0; i < listExp.size(); i++) {
			hasExp(listExp.get(i), id);
		}
        break;
	case FORALL: case EXIST:
		QuantifiedExp quantr = (QuantifiedExp) e;
		hasExp(quantr.getExp(), id);
		break;
	case WHEN:
		WhenExp whenExp = (WhenExp) e;
		hasExp(whenExp.getCondition(), id);
		hasExp(whenExp.getEffect(), id);
		break;
    case NOT:
        NotExp notExp = (NotExp) e;
		hasExp(notExp.getExp(), id);
        break;
	case TIMED_EXP:
		TimedExp timedExp = (TimedExp) e;
		hasExp(timedExp.getExp(), id);
		break;
	case IMPLY:
		ImplyExp implyExp = (ImplyExp) e;
		hasExp(implyExp.getHead(), id);
		hasExp(implyExp.getBody(), id);
		break;
	case DERIVED_PREDICATE:
		DerivedPredicate derivedPredicate = (DerivedPredicate) e;
		hasExp(derivedPredicate.getHead(), id);
		hasExp(derivedPredicate.getBody(), id);
		break;
	case F_COMP: case ASSIGN_OP: case COND_EXP: 
	case ATOMIC_FORMULA: case METRIC_EXP: case TERM:
		break;
	}
	return false;
}


static void transformEquality(PDDLObject domain, PDDLObject problem) throws InvalidExpException {
	
	// change requirments:
	//for (Iterator<RequireKey> iter = problem.requirementsIterator(); iter.hasNext(); ) {
	//}

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
		//todo: add durative actions supportk
		Action action = (Action) iter.next();
		Exp precondition = replaceEqualityOperator(action.getPrecondition(), eq_predicate);
		action.setPrecondition(precondition);
		Exp effect = replaceEqualityOperator(action.getEffect(), eq_predicate);
		action.setEffect(effect);
	}
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