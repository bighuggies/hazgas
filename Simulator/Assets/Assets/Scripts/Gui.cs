using UnityEngine;
using System.Collections;

public class Gui : MonoBehaviour {

	// Use this for initialization
	void Start () {
	
	}
	
	private int test = 5;
	
	public static Vector3 guiExclutionZone = new Vector3( 140,200,0);
	
	// Update is called once per frame
	void Update () {
		if ( test > 0 ) {
			test--;	
		}
		
		if ( test == 0 ) {
			GasIndicator.stopAlarming ();
			test--;
		}
	}
	
	private float hSliderValue = 0.5f;
	
	void OnGUI () {
		if (GUI.Button (new Rect (10,10,130,30), "Activate Alarm")) {
			GasIndicator.alarm ();
		}
		
		if ( GUI.Button (new Rect (10,40,130,30), "Reset Alarm") ) {
			GasIndicator.stopAlarming ();
		} 
		
		if ( GUI.Button (new Rect (10,70,130,30), "Clear Rooms") ) {
			foreach ( GasIndicator i in GasIndicator.rooms ) {
				i.gasVolume = 0;	
			}
		}
		
		if ( GUI.Button (new Rect (10,100,130,30), "Fill Rooms") ) {
			foreach ( GasIndicator i in GasIndicator.rooms ) {
				i.gasVolume = i.roomVolume;	
			}
		}
		
		
		
		
		// The slider for selecting the room threshold for venting.
		hSliderValue = GUI.HorizontalSlider (new Rect (10,130,130,20), hSliderValue, 0.0f, 1.0f);
		AlarmManager.pastThreshold = hSliderValue;
		
		// A slider for showing how full the frame is.
		GUI.HorizontalSlider( new Rect(10, 150, 130, 20), AlarmManager.percentage, 0f, 1f );
		
		
		// A slider for setting the fill rate.
		GasIndicator.fillRate = GUI.HorizontalSlider( new Rect(10, 170, 130, 20), GasIndicator.fillRate, 0f, 20f );
	}
}
