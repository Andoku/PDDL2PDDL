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

class DisjunctivePreconditionsTransformation extends Transformation {
	
	static void transform(PDDLObject domain, PDDLObject problem) {
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
}