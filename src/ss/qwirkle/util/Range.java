package ss.qwirkle.util;

import java.util.ArrayList;
import java.util.List;

/**
 * Container for holding a minimum and a maximum value.
 * @author Karanum
 */
public class Range {

	private Integer min;
	private Integer max;
	
	/**
	 * Creates a new empty range.
	 */
	public Range() {
		min = null;
		max = null;
	}
	
	/**
	 * Creates a new range with preset values.
	 * @param min The preset minimum
	 * @param max The preset maximum
	 */
	public Range(int min, int max) {
		this.min = min;
		this.max = max;
	}
	
	/**
	 * Copies an existing range.
	 * @param r The range that will be copied
	 */
	//@ requires r != null;
	public Range(Range r) {
		min = r.getMin().intValue();
		max = r.getMax().intValue();
	}
	
	/**
	 * Sets the minimum value.
	 * @param n The new value
	 */
	//@ ensures getMin() == n;
	public void setMin(int n) {
		min = n;
	}
	
	/**
	 * Sets the maximum value.
	 * @param n The max value
	 */
	//@ ensures getMax() == n;
	public void setMax(int n) {
		max = n;
	}
	
	/**
	 * Sets the minimum value if it is lower than the existing minimum.
	 * @param n The min value
	 */
	//@ ensures n < \old(getMin()) ==> getMin() == n;
	public void setMinIfLess(int n) {
		if (min != null) {
			min = Math.min(min, n);
		} else {
			min = n;
		}
	}
	
	/**
	 * Sets the maximum value if it is higher than the existing maximum.
	 * @param n The max value
	 */
	//@ ensures n > \old(getMax()) ==> getMax() == n;
	public void setMaxIfMore(int n) {
		if (max != null) {
			max = Math.max(max, n);
		} else {
			max = n;
		}
	}
	
	/**
	 * Returns the minimum value.
	 */
	//@ pure
	public Integer getMin() {
		return min != null ? min : Integer.MAX_VALUE;
	}
	
	/**
	 * Returns the maximum value.
	 */
	//@ pure
	public Integer getMax() {
		return max != null ? max : Integer.MIN_VALUE;
	}
	
	/**
	 * Returns a list of all integers in between the minimum and maximum values, inclusive.
	 */
	//@ pure
	public List<Integer> forEach() {
		List<Integer> iterator = new ArrayList<Integer>();
		for (int i = min; i <= max; ++i) {
			iterator.add(i);
		}
		return iterator;
	}
	
	/**
	 * Combines this range with another range.
	 * @param r The range to combine with
	 * @return The combined range
	 */
	//@ requires r != null;
	//@ ensures \result.getMin() == Math.min(getMin(), r.getMin());
	//@ ensures \result.getMax() == Math.max(getMax(), r.getMax());
	//@ pure
	public Range combine(Range r) {
		Range result = new Range(this);
		Integer rMin = r.getMin();
		Integer rMax = r.getMax();
		result.setMinIfLess(rMin);
		result.setMaxIfMore(rMax);
		return result;
	}
}
