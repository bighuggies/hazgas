using UnityEngine;
using System.Collections;

public class CameraControl : MonoBehaviour {
	
	public float speed;
	
	public float maxRotationRate;
	
	// Use this for initialization
	void Start () {
	
	}
	
	private Vector3 lastMouse;
	
	// Update is called once per frame
	void Update () {
		Vector3 dir = Vector3.zero;
		
		if ( Input.GetKey (KeyCode.W) ) {
			dir += Vector3.forward;
		}
		
		if ( Input.GetKey (KeyCode.A) ) {
			dir += Vector3.left;	
		}
		
		if ( Input.GetKey (KeyCode.D) ) {
			dir += Vector3.right;	
		}
		
		if ( Input.GetKey (KeyCode.S) ) {
			dir += Vector3.back;	
		}
		
		dir = dir.normalized;
		
		dir *= speed * Time.deltaTime;
		
		transform.Translate (dir);
		
		if ( Input.GetMouseButtonDown (1) ) {
			Screen.showCursor = false;
		}
		
		if ( Input.GetMouseButtonUp(1) ) {
			Screen.showCursor = true;	
		}
		
		// Work out the difference in the mouses position from last time.
		if ( Input.GetMouseButton (1) ) {
			
			Vector3 currentMouse = Input.mousePosition;
			
			float deltaX = currentMouse.x - lastMouse.x;
			float rotationAmount = maxRotationRate * ( deltaX / 100f) * Time.deltaTime;
			transform.RotateAround (Vector3.up, rotationAmount);
			
			float deltaY = currentMouse.y - lastMouse.y;
			rotationAmount = maxRotationRate * ( deltaY / 100f ) * Time.deltaTime;
			Camera.main.transform.Rotate( -rotationAmount*(180f/3.14158f), 0, 0);
			
		}
		
		lastMouse = Input.mousePosition;
		
	}
}
