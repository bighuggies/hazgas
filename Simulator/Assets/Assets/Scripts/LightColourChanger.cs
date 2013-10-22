using UnityEngine;
using System.Collections;

public class LightColourChanger : MonoBehaviour {
	
	private Light lightComponent;
	
	// Use this for initialization
	void Start () {
		lightComponent = GetComponent<Light>();
		lightComponent.intensity = 0;
	}
	
	// Update is called once per frame
	void Update () {
	
		if ( GasIndicator.alarming ) {
			lightComponent.enabled = true;
			transform.RotateAround (Vector3.up, 2 * Time.deltaTime);
			if ( lightComponent.intensity < 0.5f ) {
				lightComponent.intensity += 0.3f * Time.deltaTime;	
			}
		} else {
			if ( lightComponent.intensity >= 0f ) {
				lightComponent.intensity -= 0.3f * Time.deltaTime;	
			}
		}
	}
}
