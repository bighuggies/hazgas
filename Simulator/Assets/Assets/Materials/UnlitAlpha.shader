Shader "Custom/UnlitAlpha" {
	Properties {
		_MainTex ("Base (RGBA)", 2D) = "white" {}
		_Alpha ("Alpha", float) = 0.5
	}
	SubShader {
		Tags {"Queue"="Transparent"}
		LOD 100
		
		Pass {
			Lighting Off
			
			Blend SrcAlpha OneMinusSrcAlpha
			
			SetTexture [_MainTex] {
                constantColor (1, 1, 1, [_Alpha])
           		combine texture * constant
			} 
		}
	}
}
