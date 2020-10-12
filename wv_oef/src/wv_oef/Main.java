package wv_oef;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Queue;

public class Main {
	
	public static void main(String[] args) {
		System.out.println(System.getProperty("user.dir"));
		Term[] possibleTerms = getPossibleTerms();
		sumUpTerms(possibleTerms, 2);
	}
	
	public static Term[] getPossibleTerms() {
		Term a= new Term(0,"a");
		Term f= new Term(3,"f");
		Term g= new Term(2,"g");
		return new Term[] {a,f,g};
	}
	
	
	
	/*
	 * Zoekt alle constanten in de rij van termen
	 */
	public static ArrayList<Term> getConstants(Term[]  possibleTerms) {
		ArrayList<Term> constants = new ArrayList<Term>();
		for (int i=0; i< possibleTerms.length; i++) {
			if(possibleTerms[i].getKardinaliteit()==0) {
				constants.add(possibleTerms[i]);
			}
		}
		return constants;
	}
	
	/*
	 * Geeft alle predikaten terug (kardinaliteit groter dan 0
	 */
	public static ArrayList<Term> getPredicates(Term[]  possibleTerms ) {
		ArrayList<Term> predicates = new ArrayList<Term>();
		for (int i=0; i< possibleTerms.length; i++) {
			if(possibleTerms[i].getKardinaliteit()>0) {
				predicates.add(possibleTerms[i]);
			}
		}
		return predicates;
	}
	/*
	 * De bedoeling is dat we alle mogelijke termen opsommen, dit doe ik door voor elke functor variabele in te vullen
	 * Om te voorkomen dat je 2 keer hetzelfde krijgt maak ik een lijst met nieuw gevonden functoren en een lijst met alle functoren.
	 */
	public static void sumUpTerms(Term[] possibleTerms,int limit) {
		Queue<Term> queueTerms = new LinkedList<Term>();
		for(int i=0; i<possibleTerms.length;i++) {
			queueTerms.add(possibleTerms[i]);
		}
		while(limit!=0) {
			Term firstTerm =queueTerms.poll();
			if(firstTerm.groundedTerm()) {
				System.out.println(firstTerm.toString());
				limit=limit-1;
			}
			else {
				for(int i=0; i<possibleTerms.length;i++) {
					Term newTerm= firstTerm.clone();
					Term termToChange = getVariabeleTerm(newTerm,newTerm,null);
					termToChange.getInterneTerm()[getNullIndex(termToChange.getInterneTerm())]=possibleTerms[i];//TODO aanpassen voor kardinaliteit groter dan 1
					queueTerms.add(newTerm);		
				}
				
			}
		}
	}
	
	public static Term getVariabeleTerm(Term currentterm, Term previousterm,Term solution) {
		if(currentterm==null) {
			solution=previousterm;
			return solution;
		}
		if(currentterm.getKardinaliteit()==0) {
			return null;
		}
		for (int i=0; i<currentterm.getKardinaliteit() && solution==null;i++) {
			solution=getVariabeleTerm(currentterm.getInterneTerm()[i], currentterm, solution);
		}
		return solution;
		
	}
	
	public static <T> int getNullIndex(T[] list) {
		for (int i=0; i<list.length ;i++) {
			if (list[i]==null) {
				return i;
			}
		}
		return -1;
	}
	
	public static void printTerms(ArrayList<Term> terms) {
		for (int i=0; i<terms.size();i++) {
			System.out.println(terms.get(i).toString());
		}
	}
	
	

	
}
