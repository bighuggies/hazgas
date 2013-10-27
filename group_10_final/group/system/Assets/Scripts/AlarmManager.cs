using UnityEngine;
using System.Collections;
using System.Collections.Generic;

public class AlarmManager : MonoBehaviour {
	
	private LinkedList<bool> ventingFrame = new LinkedList<bool>();
	
	public int frameSize = 800;
	
	public static float percentage;
	
	public static float pastThreshold;
	
	// Use this for initialization
	void Start () {
		
	}
	
	// Update is called once per frame
	void Update () {
		// For this frame, work out how many rooms are venting
		int numVenting = 0;
		foreach ( GasIndicator i in GasIndicator.rooms ) {
			if ( i.venting && i.gasVolume > 1 ) {
				numVenting ++;
			}
		}
		
		// if more than N rooms are venting, then we need to mark this frame.
		bool overThreshold = false;
		if ( numVenting > GasIndicator.ventingThreshold ) {
			overThreshold = true;
		}
		
		// Maintain a view of the past M frames using a circular buffer.
		ventingFrame.AddFirst(overThreshold);	
		if ( ventingFrame.Count > frameSize ) {
			ventingFrame.RemoveLast ();
		}
		
		// Work out what proportion of the past M frames have been venting
		float ticksNotVenting = 0;
		float ticksVenting = 0;
		foreach ( bool b in ventingFrame ) {
			if (b) {
				ticksVenting++;
			} else {
				ticksNotVenting++;
			}
		}
		
		percentage = ( ticksVenting / ( ticksVenting+ticksNotVenting) );
		Debug.Log (percentage);
		if ( percentage >= pastThreshold ) {
			// If more than a given percentage of the past M frames have been marked, start alarming.
			// the alarm continues until it is reset by the user.
			GasIndicator.alarm ();	
		}
	}
}
