using UnityEngine;
using System.Collections;
using System.Collections.Generic;

public class GasIndicator : MonoBehaviour {
	
	public float ceilingLevel; // What is the ceiling level of the room?
	public float height; // How high is the room
	private float gasLevel; // 0 = empty, 1 = full.
	
	public static float fillRate = 20;
	
	public float roomVolume;
	public float gasVolume;
	
	public const float gasThreshold = 0.8f;
	public const float gasMinThreshold = 0.1f;
	
	// Indicates how many are currently venting.
	public static int numVenting;
	// If we are over the venting threshold, alarm instead of venting.
	public const int ventingThreshold = 0;
	// Are we venting 
	public bool venting;
	
	public static List<GasIndicator> rooms = new List<GasIndicator>();
	
	// Indicates if the system is alarming.
	public static bool alarming;
	public static int numClear;
	
	// A count of the total number of rooms which exist.
	public static int numRooms;
	
	public bool empty;
	
	// Use this for initialization
	void Start () {
		numRooms++;
		rooms.Add (this);
	}
	
	void startVenting() {
		numVenting++;
		venting = true;
		Debug.Log ("A room is starting to vent.");
		Debug.Log ( numVenting );
		empty = false;
		
		/*if ( numVenting > ventingThreshold ) {
			alarm ();
		}*/
	}
	
	public static void alarm() {
		Debug.Log ("Starting to alarm!");
		alarming = true;
		numClear = 0;
	}
	
	public static void stopAlarming() {
		alarming = false;
		foreach ( GasIndicator i in rooms ) {
			i.venting = false;
		}
	}
	
	private void vent() {
		gasVolume -= 30 * Time.deltaTime;
	}
	
	public bool full() {
		return ( gasVolume /roomVolume ) > gasThreshold;	
	}
	
	// Update is called once per frame
	void Update () {
		
		// Set the volume of the room based on the scale of the room.
		roomVolume = Mathf.Abs (transform.lossyScale.x) * Mathf.Abs (transform.lossyScale.z) * 4f;
		if ( roomVolume < 4f ) {
			// Ensure we have a minimum room volume so that divide by zero issues are ignored.
			roomVolume = 4f;
		}
		
		// Work out the gas level - how full the room is of gas as a %.
		gasLevel = gasVolume / roomVolume;
		if ( gasLevel < 0 ) {
			gasVolume = 0;
			gasLevel = 0;
		}
		if ( gasLevel > 1 ) {
			gasLevel = 1;
			gasVolume = roomVolume;
		}
		
		// This updates the gas visualisation stuff.
		float desiredY = ceilingLevel - ( height * gasLevel * 0.5f );
		Vector3 pos = transform.position;
		pos.y = desiredY;
		transform.position = pos;
		
		// Adjust the scale of this object.
		Vector3 scale = transform.localScale;
		scale.y = height * gasLevel;
		transform.localScale = scale;
		
		// set the opacity of the material.
		renderer.material.SetFloat ("_Alpha", (gasLevel/1.2f) + (1f/6f));
		
		
		
		// Add/remove gas depending on what's going on.
		// If we are alarming, vent the room.
		if ( alarming ) {
			vent ();
		} else {
			// Otherwise, if we are venting the room, vent until we are below the specified threshold.
			if ( venting ) {
				if ( gasLevel > gasMinThreshold ) {
					vent ();
				} else {
					// If we're below the threshold, stop venting.
					venting = false;
					numVenting--;
				}
				
			} else {
				//We aren't alarming and we're not venting - 
				gasVolume += fillRate * Time.deltaTime;
				if ( gasLevel > gasThreshold ) {
					startVenting ();
				}
			}
		}
		
		
	}
}
