using UnityEngine;
using System.Collections;

public class PipeReleaseControl : MonoBehaviour {
	
	private ParticleSystem sys;
	
	// Use this for initialization
	void Start () {
		sys = GetComponent<ParticleSystem>();
		sys.emissionRate = 0;
	}
	
	// Update is called once per frame
	void Update () {
		// If anything is venting, go slowly.
		
		if (GasIndicator.alarming ) {
			sys.emissionRate = 12;
		} else {
			int venting = 0;
			
			foreach ( GasIndicator i in GasIndicator.rooms ) {
				if ( i.venting ) {
					venting++;
					if ( venting > 10 ) {
						break;	
					}
				}
			}
			
			sys.emissionRate = venting;
			
		}
	}
}
