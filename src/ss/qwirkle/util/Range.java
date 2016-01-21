package ss.qwirkle.util;

import java.util.ArrayList;
import java.util.List;

public class Range {

	private Integer min;
	private Integer max;
	
	public Range() {
		min = null;
		max = null;
	}
	
	public Range(int min, int max) {
		this.min = min;
		this.max = max;
	}
	
	public void setMin(int n) {
		min = n;
	}
	
	public void setMax(int n) {
		max = n;
	}
	
	public void setMinIfLess(int n) {
		if (min != null) {
			min = Math.min(min, n);
		} else {
			min = n;
		}
	}
	
	public void setMaxIfMore(int n) {
		if (max != null) {
			max = Math.max(max, n);
		} else {
			max = n;
		}
	}
	
	public int getMin() {
		return min;
	}
	
	public int getMax() {
		return max;
	}
	
	public List<Integer> forEach() {
		List<Integer> iterator = new ArrayList<Integer>();
		for (int i = min; i <= max; ++i) {
			iterator.add(i);
		}
		return iterator;
	}
	
}
