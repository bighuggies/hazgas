using UnityEngine;
using System.Collections;

public class RoomCreation : MonoBehaviour {
	
	
	public Collider ground;
	
	private Vector3 start, end;
	
	private GameObject room;
	private GameObject roomGI;
	
	public float createdRoomHeight;
	
	private bool makingRoom;
	
	// Use this for initialization
	void Start () {
		makingRoom = false;
	}
	
	private Vector3 getMousePosition() {
		Ray r = Camera.main.ScreenPointToRay(Input.mousePosition);
		RaycastHit hit;
		Debug.DrawRay(r.origin, r.direction);
		if ( ground.Raycast( r, out hit, 9999999f ) ) {
			return hit.point;
		} else {
			return Vector3.zero;	
		}
	}
	
	// Update is called once per frame
	void Update () {
		
		Vector3 pos = Input.mousePosition;
		
		//Debug.Log ( pos.x + ":" + Gui.guiExclutionZone.x + "     " + pos.y + ":" + (Screen.height - Gui.guiExclutionZone.y));
		
		
		
		if ( Input.GetMouseButtonDown(0) ) {
			start = getMousePosition ();
			if ( pos.x > Gui.guiExclutionZone.x || pos.y < (Screen.height - Gui.guiExclutionZone.y) ) {
				room = (GameObject)Instantiate(Resources.Load("Room"));
				roomGI = (GameObject)Instantiate(Resources.Load ("GI"));
				roomGI.GetComponent<GasIndicator>().ceilingLevel = createdRoomHeight;
				makingRoom = true;
			}
		}
		
		if ( Input.GetMouseButton (0) && makingRoom ) {
			end = getMousePosition ();
			room.transform.position = new Vector3( 0.5f*(start.x+end.x), 0.5f*(start.y+end.y), 0.5f*(start.z+end.z));
			room.transform.localScale = new Vector3( (start.x-end.x), createdRoomHeight, (start.z-end.z));
			roomGI.transform.position = new Vector3( 0.5f*(start.x+end.x), 0.5f*(start.y+end.y), 0.5f*(start.z+end.z));
			roomGI.transform.localScale = new Vector3( (start.x-end.x), 1f, (start.z-end.z));
		}
		
		if ( Input.GetMouseButtonUp (0) && makingRoom ) {
			Debug.Log ("Ended!");
			room = null;
			start = Vector3.zero;
			end = Vector3.zero;
			makingRoom = false;
		}
	}
}
