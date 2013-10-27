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
		int numVenting = 0;
		foreach ( GasIndicator i in GasIndicator.rooms ) {
			if ( i.venting && i.gasVolume > 1 ) {
				numVenting ++;
			}
		}
		
		
		bool overThreshold = false;
		if ( numVenting > GasIndicator.ventingThreshold ) {
			overThreshold = true;
		}
		
		ventingFrame.AddFirst(overThreshold);	
		if ( ventingFrame.Count > frameSize ) {
			ventingFrame.RemoveLast ();
		}
		
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
			GasIndicator.alarm ();	
		}
	}
}
